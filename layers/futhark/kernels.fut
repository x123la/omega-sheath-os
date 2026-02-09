-- OMEGA analytics kernels (Fixed-point i32, scaled by 1000).

def jitter_spectrum [w][n][f] (x: [w][n][f]i32) : [w][n]i32 =
  map (\win -> map (\row -> 
    let sum_sq = reduce (+) 0 (map (\v -> (v * v) / 1000) row)
    in i32.f32 (f32.sqrt (f32.i32 sum_sq)) * 31 -- Approx sqrt in fixed-point
  ) win) x

def obstruction_clusters [w][n] (m: [w][n]i32) : [w][n]i32 =
  map (\row -> map (\v -> if v > 500 then 1 else 0) row) m

def frontier_drift [w][n] (d: [w][n]i32) : [w]i32 =
  map (\row -> reduce (+) 0 row / i32.i64 (length row)) d

def latency_surface [w][n] (l: [w][n]i32) : [w][n]i32 =
  map (\row ->
    let maxv = reduce i32.max 0 row
    in map (\v -> if maxv == 0 then 0 else (v * 1000) / maxv) row
  ) l
