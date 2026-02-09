-- OMEGA analytics kernels (advisory only).

def jitter_spectrum [w][n][f] (x: [w][n][f]f32) : [w][n]f32 =
  map (\win -> map (\row -> f32.sqrt (reduce (+) 0 (map (\v -> v*v) row))) win) x

def obstruction_clusters [w][n] (m: [w][n]f32) : [w][n]i32 =
  map (\row -> map (\v -> if v > 0.5f32 then 1 else 0) row) m

def frontier_drift [w][n] (d: [w][n]f32) : [w]f32 =
  map (\row -> reduce (+) 0 row / f32.i64 (length row)) d

def latency_surface [w][n] (l: [w][n]f32) : [w][n]f32 =
  map (\row ->
    let maxv = reduce f32.max 0f32 row
    in map (\v -> if maxv == 0f32 then 0f32 else v / maxv) row
  ) l
