// SPDX-License-Identifier: GPL-2.0-only
// Adapted from SpartanPort's iced-x86 scanner:
// https://github.com/FelipePrado0/SpartanPort/blob/main/launcher-rust/src/runner/isa_rewrite.rs
// Modified for Lantern Engine: read BBPROBE5, rewrite MOVBE/BMI1/LZCNT and selected AVX2
// integer conversions, and fail closed on other AVX2 instructions when the host lacks AVX2.


use std::collections::{HashMap, HashSet, VecDeque};
use std::env;
use std::fs;
use std::path::{Path, PathBuf};

use iced_x86::{Code, CpuidFeature, Decoder, DecoderOptions, FlowControl, Instruction, Mnemonic, OpKind, Register};
use sha2::{Digest, Sha256};

const MAGIC: &[u8; 8] = b"G3ISA1\0\0";
const NO_REG: u8 = 0xff;
const HEADER_SIZE: usize = 64;
const RECORD_SIZE: usize = 64;
const MAX_INSTRUCTION: usize = 15;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Kind {
    MovbeLoad,
    MovbeStore,
    Lzcnt,
    Tzcnt,
    Andn,
    Bextr,
    Blsi,
    Blsmsk,
    Blsr,
    Vpmovsxbw,
    Vpmovsxbd,
    Vpmovsxbq,
    Vpmovsxwd,
    Vpmovsxwq,
    Vpmovsxdq,
    Vpmovzxbw,
    Vpmovzxbd,
    Vpmovzxbq,
    Vpmovzxwd,
    Vpmovzxwq,
    Vpmovzxdq,
    Avx2Unsupported,
}

impl Kind {
    fn id(self) -> u8 {
        match self {
            Self::MovbeLoad => 1,
            Self::MovbeStore => 2,
            Self::Lzcnt => 3,
            Self::Tzcnt => 4,
            Self::Andn => 5,
            Self::Bextr => 6,
            Self::Blsi => 7,
            Self::Blsmsk => 8,
            Self::Blsr => 9,
            Self::Vpmovsxbw => 10,
            Self::Vpmovsxbd => 11,
            Self::Vpmovsxbq => 12,
            Self::Vpmovsxwd => 13,
            Self::Vpmovsxwq => 14,
            Self::Vpmovsxdq => 15,
            Self::Vpmovzxbw => 16,
            Self::Vpmovzxbd => 17,
            Self::Vpmovzxbq => 18,
            Self::Vpmovzxwd => 19,
            Self::Vpmovzxwq => 20,
            Self::Vpmovzxdq => 21,
            Self::Avx2Unsupported => 22,
        }
    }

    fn set(self) -> &'static str {
        match self {
            Self::MovbeLoad | Self::MovbeStore => "MOVBE",
            Self::Lzcnt => "LZCNT",
            Self::Tzcnt | Self::Andn | Self::Bextr | Self::Blsi | Self::Blsmsk | Self::Blsr => "BMI1",
            Self::Vpmovsxbw | Self::Vpmovsxbd | Self::Vpmovsxbq | Self::Vpmovsxwd |
            Self::Vpmovsxwq | Self::Vpmovsxdq | Self::Vpmovzxbw | Self::Vpmovzxbd |
            Self::Vpmovzxbq | Self::Vpmovzxwd | Self::Vpmovzxwq | Self::Vpmovzxdq |
            Self::Avx2Unsupported => "AVX2",
        }
    }

    fn is_vector_conversion(self) -> bool {
        matches!(self,
            Self::Vpmovsxbw | Self::Vpmovsxbd | Self::Vpmovsxbq | Self::Vpmovsxwd |
            Self::Vpmovsxwq | Self::Vpmovsxdq | Self::Vpmovzxbw | Self::Vpmovzxbd |
            Self::Vpmovzxbq | Self::Vpmovzxwd | Self::Vpmovzxwq | Self::Vpmovzxdq)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Mode {
    Jmp = 0,
    JmpRelocate = 1,
    Int3 = 2,
    Unsupported = 3,
}

#[derive(Clone, Debug)]
struct Site {
    offset: u64,
    length: u8,
    kind: Kind,
    width: u8,
    mode: Mode,
    dst: u8,
    src1: u8,
    src2: u8,
    mem_slot: u8,
    base: u8,
    index: u8,
    scale: u8,
    mem_flags: u8,
    disp: i64,
    original: [u8; MAX_INSTRUCTION],
    relocated: Vec<u8>,
}

#[derive(Clone, Copy, Debug)]
struct Segment {
    address: u64,
    size: u64,
    flags: u64,
}

fn take_u64(data: &[u8], at: &mut usize) -> Result<u64, String> {
    let end = at.checked_add(8).ok_or("linked image offset overflow")?;
    let bytes = data.get(*at..end).ok_or("truncated linked image metadata")?;
    *at = end;
    Ok(u64::from_le_bytes(bytes.try_into().map_err(|_| "invalid uint64")?))
}

fn checked_skip(data: &[u8], at: &mut usize, count: u64, width: u64) -> Result<(), String> {
    let bytes = count.checked_mul(width).ok_or("linked image metadata size overflow")?;
    let bytes = usize::try_from(bytes).map_err(|_| "linked image metadata too large")?;
    let end = at.checked_add(bytes).ok_or("linked image offset overflow")?;
    if end > data.len() {
        return Err("truncated linked image metadata".into());
    }
    *at = end;
    Ok(())
}

// Keep provenance for CFG roots. Entry points, module initializers and linked STT_FUNC
// bindings are strong roots. Image-relative relocations into executable memory are only
// candidate function pointers: they can also describe addresses of internal code/data labels.
#[derive(Default)]
struct ScanRoots {
    entry_and_init: Vec<u64>,
    function_bindings: Vec<u64>,
    relocation_candidates: Vec<u64>,
}

struct LinkedImage {
    segments: Vec<Segment>,
    image: Vec<u8>,
    roots: ScanRoots,
}

fn normalize_roots(roots: &mut Vec<u64>, segments: &[Segment]) {
    roots.retain(|address| executable_address(*address, segments));
    roots.sort_unstable();
    roots.dedup();
}

fn executable_address(address: u64, segments: &[Segment]) -> bool {
    segments.iter().any(|s| {
        s.flags & 1 != 0 && address >= s.address && address - s.address < s.size
    })
}

fn read_boot_linked(data: &[u8]) -> Result<LinkedImage, String> {
    if data.len() < 8 || (&data[..8] != b"BBPROBE5" && &data[..8] != b"G3PROBE5") {
        return Err("not a BBPROBE5 linked image".into());
    }
    let mut at = 8usize;
    let image_size = take_u64(data, &mut at)?;
    let entry = take_u64(data, &mut at)?;
    let segment_count = take_u64(data, &mut at)?;
    let reloc_count = take_u64(data, &mut at)?;
    let import_count = take_u64(data, &mut at)?;
    let _capabilities = take_u64(data, &mut at)?;

    if image_size == 0 || image_size > 512 * 1024 * 1024 ||
       segment_count == 0 || segment_count > 64 ||
       reloc_count > 1_000_000 || import_count > 100_000 {
        return Err("linked image limits exceeded".into());
    }

    let _procparam = take_u64(data, &mut at)?;
    for _ in 0..4 { let _ = take_u64(data, &mut at)?; }
    let module_count = take_u64(data, &mut at)?;
    if module_count == 0 || module_count > 16 {
        return Err("invalid linked module count".into());
    }

    let mut roots = ScanRoots { entry_and_init: vec![entry], ..ScanRoots::default() };
    for _ in 0..module_count {
        let _base = take_u64(data, &mut at)?;
        let _size = take_u64(data, &mut at)?;
        let init = take_u64(data, &mut at)?;
        let _tls_address = take_u64(data, &mut at)?;
        let _tls_memsz = take_u64(data, &mut at)?;
        let _tls_filesz = take_u64(data, &mut at)?;
        let _tls_module = take_u64(data, &mut at)?;
        if init != 0 {
            roots.entry_and_init.push(init);
        }
    }

    let binding_count = take_u64(data, &mut at)?;
    if binding_count > import_count {
        return Err("invalid native binding count".into());
    }
    for _ in 0..binding_count {
        let _import_index = take_u64(data, &mut at)?;
        let address = take_u64(data, &mut at)?;
        let kind = take_u64(data, &mut at)?;
        // link_modules.py writes kind 1 for STT_FUNC exports and kind 2 for objects.
        if kind == 1 {
            roots.function_bindings.push(address);
        }
    }

    let mut segments = Vec::with_capacity(segment_count as usize);
    for _ in 0..segment_count {
        let address = take_u64(data, &mut at)?;
        let size = take_u64(data, &mut at)?;
        let flags = take_u64(data, &mut at)?;
        if address > image_size || size > image_size - address {
            return Err("segment lies outside linked image".into());
        }
        segments.push(Segment { address, size, flags });
    }

    checked_skip(data, &mut at, import_count, 128)?;

    for _ in 0..reloc_count {
        let _target = take_u64(data, &mut at)?;
        let kind = take_u64(data, &mut at)?;
        let value = take_u64(data, &mut at)?;
        let _addend = take_u64(data, &mut at)?;
        // kind 0 is an image-relative relocation. It may be a static function pointer;
        // kinds 1 and 2 are imports/TLS and do not contain a local image code address.
        if kind == 0 {
            roots.relocation_candidates.push(value);
        }
    }

    let image_len = usize::try_from(image_size).map_err(|_| "linked image too large")?;
    let end = at.checked_add(image_len).ok_or("linked image size overflow")?;
    if end != data.len() {
        return Err("linked image is truncated or has trailing data".into());
    }

    normalize_roots(&mut roots.entry_and_init, &segments);
    normalize_roots(&mut roots.function_bindings, &segments);
    normalize_roots(&mut roots.relocation_candidates, &segments);

    Ok(LinkedImage { segments, image: data[at..end].to_vec(), roots })
}

fn kind_of(ins: &Instruction) -> Option<Kind> {
    let kind = match ins.mnemonic() {
        Mnemonic::Movbe if ins.op0_kind() == OpKind::Register => Kind::MovbeLoad,
        Mnemonic::Movbe => Kind::MovbeStore,
        Mnemonic::Lzcnt => Kind::Lzcnt,
        Mnemonic::Tzcnt => Kind::Tzcnt,
        Mnemonic::Andn => Kind::Andn,
        Mnemonic::Bextr => Kind::Bextr,
        Mnemonic::Blsi => Kind::Blsi,
        Mnemonic::Blsmsk => Kind::Blsmsk,
        Mnemonic::Blsr => Kind::Blsr,
        Mnemonic::Vpmovsxbw => Kind::Vpmovsxbw,
        Mnemonic::Vpmovsxbd => Kind::Vpmovsxbd,
        Mnemonic::Vpmovsxbq => Kind::Vpmovsxbq,
        Mnemonic::Vpmovsxwd => Kind::Vpmovsxwd,
        Mnemonic::Vpmovsxwq => Kind::Vpmovsxwq,
        Mnemonic::Vpmovsxdq => Kind::Vpmovsxdq,
        Mnemonic::Vpmovzxbw => Kind::Vpmovzxbw,
        Mnemonic::Vpmovzxbd => Kind::Vpmovzxbd,
        Mnemonic::Vpmovzxbq => Kind::Vpmovzxbq,
        Mnemonic::Vpmovzxwd => Kind::Vpmovzxwd,
        Mnemonic::Vpmovzxwq => Kind::Vpmovzxwq,
        Mnemonic::Vpmovzxdq => Kind::Vpmovzxdq,
        _ if ins.cpuid_features().contains(&CpuidFeature::AVX2) => Kind::Avx2Unsupported,
        _ => return None,
    };
    Some(kind)
}

fn register_number(register: Register) -> u8 {
    if register == Register::None { NO_REG } else { register.number() as u8 }
}

fn vector_register_number(register: Register) -> u8 {
    let first = if register.size() == 16 { Register::XMM0.number() } else { Register::YMM0.number() };
    register.number().saturating_sub(first) as u8
}

fn site_register_number(kind: Kind, register: Register) -> u8 {
    if kind.is_vector_conversion() && (register.size() == 16 || register.size() == 32) {
        vector_register_number(register)
    } else {
        register_number(register)
    }
}

fn site_of(ins: &Instruction, kind: Kind, bytes: &[u8]) -> Site {
    let mut registers = [NO_REG; 3];
    let mut mem_slot = 0;
    let mut width = 0;
    for operand in 0..ins.op_count() {
        match ins.op_kind(operand) {
            OpKind::Register => {
                if kind != Kind::Avx2Unsupported {
                    let register = ins.op_register(operand);
                    if let Some(slot) = registers.get_mut(operand as usize) {
                        *slot = site_register_number(kind, register);
                    }
                    if width == 0 {
                        width = if kind.is_vector_conversion() { register.size() } else { register.size() * 8 };
                    }
                }
            }
            OpKind::Memory => mem_slot = if operand == 0 { 1 } else { 2 },
            _ => {}
        }
    }

    let [dst, src1, src2] = registers;
    let mut original = [0u8; MAX_INSTRUCTION];
    original[..bytes.len()].copy_from_slice(bytes);
    let mut site = Site {
        offset: ins.ip(),
        length: ins.len() as u8,
        kind,
        width: width as u8,
        mode: Mode::Jmp,
        dst, src1, src2, mem_slot,
        base: NO_REG,
        index: NO_REG,
        scale: 0,
        mem_flags: 0,
        disp: 0,
        original,
        relocated: Vec::new(),
    };

    if kind == Kind::Avx2Unsupported {
        site.mode = Mode::Unsupported;
        return site;
    }
    let mut unsupported = ins.segment_prefix() != Register::None || ins.has_lock_prefix();
    if mem_slot != 0 {
        unsupported |= [ins.memory_base(), ins.memory_index()]
            .iter()
            .any(|&register| register != Register::None && register.size() != 8);
        site.scale = ins.memory_index_scale() as u8;
        if ins.is_ip_rel_memory_operand() {
            site.mem_flags = 1;
            site.disp = ins.ip_rel_memory_address() as i64;
        } else {
            site.base = register_number(ins.memory_base());
            site.index = register_number(ins.memory_index());
            site.disp = ins.memory_displacement64() as i64;
        }
    }

    site.mode = if unsupported {
        Mode::Unsupported
    } else if ins.len() >= 5 {
        Mode::Jmp
    } else {
        Mode::Int3
    };
    site
}

fn is_plain(ins: &Instruction, end: u64) -> bool {
    ins.code() != Code::INVALID &&
    ins.flow_control() == FlowControl::Next &&
    !ins.is_ip_rel_memory_operand() &&
    !ins.has_rep_prefix() &&
    !ins.has_repne_prefix() &&
    kind_of(ins).is_none() &&
    ins.next_ip() <= end
}

fn scan_segment(code: &[u8], address: u64) -> Vec<Site> {
    let Ok(mut decoder) = Decoder::try_with_ip(64, code, address, DecoderOptions::NONE) else {
        return Vec::new();
    };
    let end = address.saturating_add(code.len() as u64);
    let mut sites: Vec<Site> = Vec::new();
    let mut targets = HashSet::new();
    let mut candidates = Vec::new();
    let mut pending = None;

    while decoder.can_decode() {
        let start = decoder.position();
        let ins = decoder.decode();
        let bytes = code.get(start..decoder.position()).unwrap_or_default();

        if matches!(ins.flow_control(),
            FlowControl::UnconditionalBranch | FlowControl::ConditionalBranch | FlowControl::Call)
            && ins.op0_kind() == OpKind::NearBranch64 {
            targets.insert(ins.near_branch_target());
        }

        if let Some(site) = pending.take() {
            if is_plain(&ins, end) {
                candidates.push((site, ins.ip(), bytes.to_vec()));
            }
        }

        if let Some(kind) = kind_of(&ins) {
            let site = site_of(&ins, kind, bytes);
            if site.mode == Mode::Int3 && ins.len() == 4 {
                pending = Some(sites.len());
            }
            sites.push(site);
        }
    }

    for (site, ip, relocated) in candidates {
        if let Some(site) = sites.get_mut(site).filter(|_| !targets.contains(&ip)) {
            site.mode = Mode::JmpRelocate;
            site.relocated = relocated;
        }
    }
    sites
}

// Recursive-descent control-flow scan used as a second opinion on the linear sweep.
// This is deliberately diagnostic for now: indirect branches and dynamically constructed
// function pointers can hide edges, so a site not reached from these roots is NOT yet proven
// to be data and must not be silently removed from the fail-closed rewrite table.
fn scan_reachable(segments: &[Segment], image: &[u8], roots: &[u64]) -> Vec<Site> {
    let mut queue: VecDeque<u64> = roots.iter().copied().collect();
    let mut decoded = HashSet::new();
    let mut sites: HashMap<u64, Site> = HashMap::new();

    while let Some(start) = queue.pop_front() {
        let Some(segment) = segments.iter().find(|s| {
            s.flags & 1 != 0 && start >= s.address && start - s.address < s.size
        }) else {
            continue;
        };
        let Some(offset) = usize::try_from(start).ok() else { continue; };
        let Some(segment_end) = usize::try_from(segment.address + segment.size).ok() else { continue; };
        if segment_end > image.len() || offset >= segment_end {
            continue;
        }
        let code = &image[offset..segment_end];
        let Ok(mut decoder) = Decoder::try_with_ip(64, code, start, DecoderOptions::NONE) else {
            continue;
        };

        while decoder.can_decode() {
            let byte_start = decoder.position();
            let ins = decoder.decode();
            if ins.code() == Code::INVALID {
                break;
            }
            if !decoded.insert(ins.ip()) {
                break;
            }
            let bytes = code.get(byte_start..decoder.position()).unwrap_or_default();
            if let Some(kind) = kind_of(&ins) {
                sites.entry(ins.ip()).or_insert_with(|| site_of(&ins, kind, bytes));
            }

            let direct_target = (ins.op0_kind() == OpKind::NearBranch64)
                .then(|| ins.near_branch_target());
            match ins.flow_control() {
                FlowControl::Next => {}
                FlowControl::Call | FlowControl::IndirectCall => {
                    if let Some(target) = direct_target {
                        if executable_address(target, segments) {
                            queue.push_back(target);
                        }
                    }
                    // A call returns to the next instruction. Indirect call targets are
                    // seeded separately by function bindings and image-relative relocations.
                }
                FlowControl::ConditionalBranch => {
                    if let Some(target) = direct_target {
                        if executable_address(target, segments) {
                            queue.push_back(target);
                        }
                    }
                }
                FlowControl::UnconditionalBranch => {
                    if let Some(target) = direct_target {
                        if executable_address(target, segments) {
                            queue.push_back(target);
                        }
                    }
                    break;
                }
                FlowControl::XbeginXabortXend => {
                    if let Some(target) = direct_target {
                        if executable_address(target, segments) {
                            queue.push_back(target);
                        }
                    }
                }
                FlowControl::IndirectBranch | FlowControl::Return |
                FlowControl::Interrupt | FlowControl::Exception => break,
            }
        }
    }

    let mut result: Vec<Site> = sites.into_values().collect();
    result.sort_by_key(|site| site.offset);
    result
}

fn padded(bytes: &[u8]) -> [u8; MAX_INSTRUCTION] {
    let mut out = [0u8; MAX_INSTRUCTION];
    out[..bytes.len()].copy_from_slice(bytes);
    out
}

fn encode_table(image: &[u8], sites: &[Site]) -> Result<Vec<u8>, String> {
    if sites.len() > (1 << 20) {
        return Err("too many instruction sites".into());
    }
    let mut table = Vec::with_capacity(HEADER_SIZE + RECORD_SIZE * sites.len());
    table.extend_from_slice(MAGIC);
    table.extend_from_slice(&(image.len() as u64).to_le_bytes());
    table.extend_from_slice(&Sha256::digest(image));
    table.extend_from_slice(&(sites.len() as u32).to_le_bytes());
    let unsupported = sites.iter().filter(|s| s.mode == Mode::Unsupported).count();
    table.extend_from_slice(&(unsupported as u32).to_le_bytes());
    table.extend_from_slice(&[0; 8]);

    let mut sorted: Vec<&Site> = sites.iter().collect();
    sorted.sort_by_key(|s| s.offset);
    for site in sorted {
        if site.relocated.len() > MAX_INSTRUCTION {
            return Err("relocated instruction exceeds x86 instruction length".into());
        }
        table.extend_from_slice(&site.offset.to_le_bytes());
        table.extend_from_slice(&[
            site.length, site.kind.id(), site.width, site.mode as u8,
            site.dst, site.src1, site.src2, site.mem_slot,
            site.base, site.index, site.scale, site.mem_flags,
            0, 0, 0, 0,
        ]);
        table.extend_from_slice(&site.disp.to_le_bytes());
        table.extend_from_slice(&site.original);
        table.push(site.relocated.len() as u8);
        table.extend_from_slice(&padded(&site.relocated));
        table.push(0);
    }
    Ok(table)
}

#[cfg(target_arch = "x86_64")]
fn missing_cpu_sets() -> Vec<&'static str> {
    use std::arch::x86_64::{__cpuid, __cpuid_count};
    // Use CPUID directly so this check is available in both GNU and MSVC Windows builds.
    let basic_max = __cpuid(0).eax;
    let leaf1_ecx = if basic_max >= 1 { __cpuid(1).ecx } else { 0 };
    let leaf7_ebx = if basic_max >= 7 { __cpuid_count(7, 0).ebx } else { 0 };
    let extended_max = __cpuid(0x8000_0000).eax;
    let extended_ecx = if extended_max >= 0x8000_0001 {
        __cpuid(0x8000_0001).ecx
    } else {
        0
    };
    let mut missing = Vec::new();
    if leaf1_ecx & (1 << 22) == 0 { missing.push("MOVBE"); }
    if leaf7_ebx & (1 << 3) == 0 { missing.push("BMI1"); }
    if extended_ecx & (1 << 5) == 0 { missing.push("LZCNT"); }
    if leaf7_ebx & (1 << 5) == 0 { missing.push("AVX2"); }
    missing
}

#[cfg(not(target_arch = "x86_64"))]
fn missing_cpu_sets() -> Vec<&'static str> {
    vec!["x86-64 host required"]
}

fn scan(boot: &Path, out: &Path) -> Result<String, String> {
    let missing = missing_cpu_sets();
    if missing.is_empty() {
        return Ok("CPU: native MOVBE, BMI1, LZCNT and AVX2; scanner skipped, original code will execute natively".into());
    }
    let data = fs::read(boot).map_err(|e| format!("{}: {e}", boot.display()))?;
    let linked = read_boot_linked(&data)?;
    let mut sites = Vec::new();

    for segment in linked.segments.iter().filter(|s| s.flags & 1 != 0) {
        let start = usize::try_from(segment.address).map_err(|_| "segment offset too large")?;
        let size = usize::try_from(segment.size).map_err(|_| "segment size too large")?;
        let end = start.checked_add(size).ok_or("segment range overflow")?;
        let code = linked.image.get(start..end).ok_or("executable segment outside linked image")?;
        sites.extend(scan_segment(code, segment.address));
    }

    // Run CFG analysis in two tiers. Entry/init/function-binding roots are stronger evidence;
    // relocation-derived addresses are retained as a weaker superset because not every
    // relocation into executable memory denotes a function entry.
    let mut strong_roots = linked.roots.entry_and_init.clone();
    strong_roots.extend(linked.roots.function_bindings.iter().copied());
    normalize_roots(&mut strong_roots, &linked.segments);

    let strong_reachable = scan_reachable(&linked.segments, &linked.image, &strong_roots);
    let mut all_roots = strong_roots.clone();
    all_roots.extend(linked.roots.relocation_candidates.iter().copied());
    normalize_roots(&mut all_roots, &linked.segments);
    let all_reachable = scan_reachable(&linked.segments, &linked.image, &all_roots);

    let strong_avx2 = strong_reachable.iter().filter(|site| site.kind.set() == "AVX2").count();
    let strong_unsupported = strong_reachable.iter()
        .filter(|site| site.kind.set() == "AVX2" && site.mode == Mode::Unsupported).count();
    let all_avx2 = all_reachable.iter().filter(|site| site.kind.set() == "AVX2").count();
    let all_unsupported = all_reachable.iter()
        .filter(|site| site.kind.set() == "AVX2" && site.mode == Mode::Unsupported).count();
    let all_offsets: HashSet<u64> = all_reachable.iter().map(|site| site.offset).collect();
    let linear_only_unsupported = sites.iter()
        .filter(|site| site.kind.set() == "AVX2" && site.mode == Mode::Unsupported &&
                       !all_offsets.contains(&site.offset)).count();
    let weak_roots = all_roots.len().saturating_sub(strong_roots.len());

    let table = encode_table(&linked.image, &sites)?;
    fs::create_dir_all(out).map_err(|e| format!("{}: {e}", out.display()))?;
    let target = out.join("isa-rewrite.bin");
    let temporary = out.join("isa-rewrite.bin.tmp");
    fs::write(&temporary, table).map_err(|e| format!("{}: {e}", temporary.display()))?;
    if target.exists() {
        fs::remove_file(&target).map_err(|e| format!("{}: {e}", target.display()))?;
    }
    fs::rename(&temporary, &target).map_err(|e| format!("{}: {e}", target.display()))?;

    let count_set = |set: &str| sites.iter().filter(|s| s.kind.set() == set).count();
    let relocated = sites.iter().filter(|s| s.mode == Mode::JmpRelocate).count();
    let int3 = sites.iter().filter(|s| s.mode == Mode::Int3).count();
    let unsupported = sites.iter().filter(|s| s.mode == Mode::Unsupported).count();
    Ok(format!(
        "CPU missing {}; ISA: {} sites (MOVBE {}, BMI1 {}, LZCNT {}, AVX2 {}); {} relocated, {} int3, {} unsupported\n\
         ISA CFG: {} strong roots ({} entry/init, {} function bindings): {} AVX2 ({} unsupported); +{} relocation roots: {} AVX2 ({} unsupported); {} unsupported only in linear sweep",
        missing.join(", "), sites.len(), count_set("MOVBE"), count_set("BMI1"), count_set("LZCNT"),
        count_set("AVX2"), relocated, int3, unsupported, strong_roots.len(),
        linked.roots.entry_and_init.len(), linked.roots.function_bindings.len(), strong_avx2,
        strong_unsupported, weak_roots, all_avx2.saturating_sub(strong_avx2),
        all_unsupported.saturating_sub(strong_unsupported), linear_only_unsupported
    ))
}

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() != 3 {
        eprintln!("Usage: bb-isa-scan <boot-linked.bin> <output-directory>");
        std::process::exit(2);
    }
    match scan(&PathBuf::from(&args[1]), &PathBuf::from(&args[2])) {
        Ok(summary) => println!("{summary}"),
        Err(error) => {
            eprintln!("ISA: rewrite table unavailable ({error})");
            std::process::exit(1);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn bytes(hex: &str) -> Vec<u8> {
        hex.as_bytes().chunks_exact(2)
            .map(|pair| u8::from_str_radix(std::str::from_utf8(pair).unwrap(), 16).unwrap())
            .collect()
    }

    fn lantern_boot_linked(code: &[u8]) -> Vec<u8> {
        let size = code.len() as u64;
        let words = [
            size, 0, 1, 0, 0, 1,             // BBPROBE5 header
            0,                               // procparam
            0, 0, 0, 0,                      // main TLS
            1,                               // one linked module
            0, size, 0, 0, 0, 0, 0,          // module metadata
            0,                               // no native bindings
            0, size, 5,                      // one executable segment
        ];
        let mut data = b"BBPROBE5".to_vec();
        for word in words {
            data.extend_from_slice(&word.to_le_bytes());
        }
        data.extend_from_slice(code);
        data
    }

    #[test]
    fn reads_lantern_bbprobe5_and_scans_only_the_requested_instruction_sets() {
        let code = bytes("0f38f108c4e270f3c9f30fbdc1c3");
        let boot = lantern_boot_linked(&code);
        let linked = read_boot_linked(&boot).unwrap();
        assert_eq!(linked.segments.len(), 1);
        assert_eq!(linked.segments[0].address, 0);
        assert_eq!(linked.segments[0].size, code.len() as u64);
        assert_eq!(linked.segments[0].flags & 1, 1);
        assert_eq!(linked.image, code);
        assert_eq!(linked.roots.entry_and_init, vec![0]);
        assert!(linked.roots.function_bindings.is_empty());
        assert!(linked.roots.relocation_candidates.is_empty());

        let sites = scan_segment(&linked.image, 0);
        assert_eq!(sites.len(), 3);
        assert_eq!(sites[0].kind, Kind::MovbeStore);
        assert_eq!(sites[1].kind, Kind::Blsr);
        assert_eq!(sites[2].kind, Kind::Lzcnt);
    }

    #[test]
    fn keeps_relocation_targets_separate_from_strong_cfg_roots() {
        // RET at address 0 terminates the entry path. The relocation points at the following
        // bytes, which decode as VPADDD, but that address is only a weak candidate root.
        let code = bytes("c3c5f5fec2");
        let size = code.len() as u64;
        let words = [
            size, 0, 1, 1, 0, 1,       // BBPROBE5 header: one relocation
            0, 0, 0, 0,                 // procparam and main TLS
            1,                           // one module
            0, size, 0, 0, 0, 0, 0,    // module metadata
            0,                           // no native bindings
            0, size, 5,                  // executable segment
            0, 0, 1, 0,                  // relative relocation: target=0, value=1
        ];
        let mut boot = b"BBPROBE5".to_vec();
        for word in words {
            boot.extend_from_slice(&word.to_le_bytes());
        }
        boot.extend_from_slice(&code);

        let linked = read_boot_linked(&boot).unwrap();
        assert_eq!(linked.roots.entry_and_init, vec![0]);
        assert_eq!(linked.roots.relocation_candidates, vec![1]);

        let strong = scan_reachable(&linked.segments, &linked.image, &linked.roots.entry_and_init);
        assert!(strong.is_empty());

        let expanded = scan_reachable(
            &linked.segments,
            &linked.image,
            &linked.roots.relocation_candidates
        );
        assert_eq!(expanded.len(), 1);
        assert_eq!(expanded[0].kind, Kind::Avx2Unsupported);
    }

    #[test]
    fn scans_movbe_bmi1_and_lzcnt_without_f16c() {
        let code = bytes("0f38f108c4e270f3c9f30fbdc1c3");
        let sites = scan_segment(&code, 0x1000);
        assert_eq!(sites.len(), 3);
        assert_eq!(sites[0].kind, Kind::MovbeStore);
        assert_eq!(sites[1].kind, Kind::Blsr);
        assert_eq!(sites[2].kind, Kind::Lzcnt);
        assert!(sites.iter().all(|s| s.mode != Mode::Unsupported));
    }


    #[test]
    fn scans_all_avx2_sign_and_zero_extension_moves() {
        let code = bytes(
            "c4e27920c1c4e27921c1c4e27922c1c4e27923c1c4e27924c1c4e27925c1\
             c4e27930c1c4e27931c1c4e27932c1c4e27933c1c4e27934c1c4e27935c1"
                .replace(' ', "").as_str()
        );
        let sites = scan_segment(&code, 0x2000);
        assert_eq!(sites.len(), 12);
        assert_eq!(sites[0].kind, Kind::Vpmovsxbw);
        assert_eq!(sites[1].kind, Kind::Vpmovsxbd);
        assert_eq!(sites[2].kind, Kind::Vpmovsxbq);
        assert_eq!(sites[3].kind, Kind::Vpmovsxwd);
        assert_eq!(sites[4].kind, Kind::Vpmovsxwq);
        assert_eq!(sites[5].kind, Kind::Vpmovsxdq);
        assert_eq!(sites[6].kind, Kind::Vpmovzxbw);
        assert_eq!(sites[7].kind, Kind::Vpmovzxbd);
        assert_eq!(sites[8].kind, Kind::Vpmovzxbq);
        assert_eq!(sites[9].kind, Kind::Vpmovzxwd);
        assert_eq!(sites[10].kind, Kind::Vpmovzxwq);
        assert_eq!(sites[11].kind, Kind::Vpmovzxdq);
        assert!(sites.iter().all(|site| site.width == 16 && site.dst == 0 && site.src1 == 1));
        assert!(sites.iter().all(|site| site.mode != Mode::Unsupported));

        // VPMOVSXBW ymm0, xmm1 exercises 256-bit destination and 128-bit source register mapping.
        let ymm_site = scan_segment(&bytes("c4e27d20c1"), 0x2100).remove(0);
        assert_eq!(ymm_site.kind, Kind::Vpmovsxbw);
        assert_eq!(ymm_site.width, 32);
        assert_eq!(ymm_site.dst, 0);
        assert_eq!(ymm_site.src1, 1);
        assert_ne!(ymm_site.mode, Mode::Unsupported);

        // High vector register numbers must be normalized to the 0-15 YMM/XMM index range.
        let high_site = scan_segment(&bytes("c4427d20ca"), 0x2200).remove(0);
        assert_eq!(high_site.kind, Kind::Vpmovsxbw);
        assert_eq!(high_site.width, 32);
        assert_eq!(high_site.dst, 9);
        assert_eq!(high_site.src1, 10);
        assert_ne!(high_site.mode, Mode::Unsupported);
    }


    #[test]
    fn marks_other_avx2_instructions_unsupported() {
        // VPADDD ymm0, ymm1, ymm2: an AVX2 instruction not yet emulated.
        let sites = scan_segment(&bytes("c5f5fec2"), 0x3000);
        assert_eq!(sites.len(), 1);
        assert_eq!(sites[0].kind, Kind::Avx2Unsupported);
        assert_eq!(sites[0].mode, Mode::Unsupported);
        assert_eq!(sites[0].dst, NO_REG);
        assert_eq!(sites[0].src1, NO_REG);
        assert_eq!(sites[0].src2, NO_REG);
    }

    #[test]
    fn control_flow_scan_ignores_avx2_bytes_after_return() {
        // This is data, not an instruction path: RET is the only instruction reachable
        // from the supplied root, although a linear sweep decodes VPADDD in the following bytes.
        let code = bytes("c3c5f5fec2");
        let segment = Segment { address: 0, size: code.len() as u64, flags: 5 };
        let linear = scan_segment(&code, 0);
        assert_eq!(linear.len(), 1);
        assert_eq!(linear[0].kind, Kind::Avx2Unsupported);

        let reachable = scan_reachable(&[segment], &code, &[0]);
        assert!(reachable.is_empty());
    }

    #[test]
    fn control_flow_scan_follows_direct_calls_to_avx2_sites() {
        // CALL +5 at 0 enters the function at 10; the caller's RET prevents fall-through
        // into the padding. The AVX2 instruction is reached only through the call edge.
        let code = bytes("e805000000c390909090c5f5fec2c3");
        let segment = Segment { address: 0, size: code.len() as u64, flags: 5 };
        let reachable = scan_reachable(&[segment], &code, &[0]);

        assert_eq!(reachable.len(), 1);
        assert_eq!(reachable[0].offset, 10);
        assert_eq!(reachable[0].kind, Kind::Avx2Unsupported);
        assert_eq!(reachable[0].mode, Mode::Unsupported);
    }

    #[test]
    fn writes_the_loader_record_layout() {
        let image = bytes("c4e270f3c9");
        let site = scan_segment(&image, 0).remove(0);
        let table = encode_table(&image, &[site]).unwrap();
        assert_eq!(&table[..8], MAGIC);
        assert_eq!(&table[8..16], (image.len() as u64).to_le_bytes());
        assert_eq!(u32::from_le_bytes(table[48..52].try_into().unwrap()), 1);
        assert_eq!(table.len(), HEADER_SIZE + RECORD_SIZE);
    }
}
