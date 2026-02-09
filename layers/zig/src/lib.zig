const std = @import("std");

pub const OmegaFileHeader = packed struct {
    magic: [8]u8,
    schema_version: u16,
    endian_flag: u8,
    hash_alg_id: u8,
    reserved0: [14]u8,
    schema_hash: [32]u8,
    reserved1: [6]u8,
};

pub const FrameHeader = packed struct {
    frame_len: u32,
    frame_crc32: u32,
    frame_type: u16,
    reserved: u16,
};

pub fn crc32Frame(frame_type: u16, reserved: u16, payload: []const u8) u32 {
    var hasher = std.hash.Crc32.init();
    hasher.update(std.mem.asBytes(&frame_type));
    hasher.update(std.mem.asBytes(&reserved));
    hasher.update(payload);
    return hasher.final();
}

// CRITICAL: Manual parsing deleted.
// TODO: Link against schemas/omega.capnp using generic Zig C-ABI.
// Do not restore manual byte slicing.
pub fn verifyFrame(header: FrameHeader, payload: []const u8) bool {
    _ = header;
    _ = payload;
    @panic("Manual parsing disabled. Use Cap'n Proto schema bindings.");
}

pub fn recoverValidPrefix(bytes: []const u8) usize {
    _ = bytes;
    @panic("Manual parsing disabled. Use Cap'n Proto schema bindings.");
}

test "frame crc" {
    const payload = "omega";
    const crc = crc32Frame(1, 0, payload);
    try std.testing.expect(crc != 0);
}
