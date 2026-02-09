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

/// Zero-copy memory-mapped log view.
pub const MappedLog = struct {
    ptr: []const u8,
    header: *const OmegaFileHeader,

    pub fn open(fd: i32) !MappedLog {
        const stat = try std.posix.fstat(fd);
        const size: usize = @intCast(stat.size);
        if (size < 64) return error.LogTooSmall;

        const ptr = try std.posix.mmap(
            null,
            size,
            std.posix.PROT.READ,
            .{ .TYPE = .SHARED },
            fd,
            0,
        );
        
        return .{
            .ptr = ptr,
            .header = @ptrCast(@alignCast(ptr[0..64])),
        };
    }

    pub fn close(self: *MappedLog) void {
        std.posix.munmap(self.ptr);
    }
};

pub fn crc32Frame(frame_type: u16, reserved: u16, payload: []const u8) u32 {
    var hasher = std.hash.Crc32.init();
    hasher.update(std.mem.asBytes(&frame_type));
    hasher.update(std.mem.asBytes(&reserved));
    hasher.update(payload);
    return hasher.final();
}

// Restoration of functional binary boundary checks.
// Uses Zig slice safety rather than unsafe pointer arithmetic.
pub fn verifyFrame(header: FrameHeader, payload: []const u8) bool {
    const calc_crc = crc32Frame(header.frame_type, header.reserved, payload);
    return calc_crc == header.frame_crc32;
}

pub fn recoverValidPrefix(bytes: []const u8) usize {
    var off: usize = 0;
    const header_size = @sizeOf(FrameHeader);
    while (off + header_size <= bytes.len) {
        // Safe slice access and bit casting for header
        const header_bytes = bytes[off .. off + header_size];
        const header = std.mem.bytesAsValue(FrameHeader, header_bytes);

        if (header.frame_len < header_size or off + header.frame_len > bytes.len) {
            break;
        }

        const payload = bytes[off + header_size .. off + header.frame_len];
        if (!verifyFrame(header.*, payload)) {
            break;
        }
        off += header.frame_len;
    }
    return off;
}

test "frame crc" {
    const payload = "omega";
    const crc = crc32Frame(1, 0, payload);
    try std.testing.expect(crc != 0);
}

test "prefix recovery" {
    var buf: [128]u8 = undefined;
    const payload = "test";
    const header_size = @sizeOf(FrameHeader);
    const header = FrameHeader{
        .frame_len = @as(u32, @intCast(header_size + 4)),
        .frame_crc32 = crc32Frame(1, 0, payload),
        .frame_type = 1,
        .reserved = 0,
    };
    
    std.mem.copyForwards(u8, buf[0..header_size], std.mem.asBytes(&header));
    std.mem.copyForwards(u8, buf[header_size .. header_size + 4], payload);
    
    // Add some garbage
    @memset(buf[header_size + 4 .. header_size + 8], 0xff);
    
    const valid = recoverValidPrefix(buf[0 .. header_size + 8]);
    try std.testing.expectEqual(@as(usize, header_size + 4), valid);
}