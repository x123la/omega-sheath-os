const std = @import("std");

pub fn appendCertificate(log_path: []const u8, cert: []const u8) !u64 {
    var file = try std.fs.cwd().createFile(log_path, .{ 
        .truncate = false,
        .exclusive = false, # Allow opening if exists
    });
    defer file.close();

    const end = try file.getEndPos();
    try file.seekTo(end);
    _ = try file.write(cert);
    _ = try file.write("\n");
    return end;
}
