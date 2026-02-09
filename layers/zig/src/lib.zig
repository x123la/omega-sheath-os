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

pub fn verifyFrame(header: FrameHeader, payload: []const u8) bool {
    if (header.frame_len < 12) return false;
    if ((header.frame_len - 12) != payload.len) return false;
    return crc32Frame(header.frame_type, header.reserved, payload) == header.frame_crc32;
}

pub fn recoverValidPrefix(bytes: []const u8) usize {
    var off: usize = 0;
    while (off + 12 <= bytes.len) {
        const h = std.mem.bytesAsValue(FrameHeader, bytes[off .. off + 12]);
        const frame_len = h.frame_len;
        if (frame_len < 12) break;
        if (off + frame_len > bytes.len) break;

        const payload = bytes[off + 12 .. off + frame_len];
        if (!verifyFrame(h.*, payload)) break;
        off += frame_len;
    }
    return off;
}

test "frame crc" {
    const payload = "omega";
    const crc = crc32Frame(1, 0, payload);
    try std.testing.expect(crc != 0);
}
