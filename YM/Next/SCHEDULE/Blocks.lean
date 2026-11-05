import YM.Next.SCHEDULE.Dues

/-!
# Numeric windows for the two weak reflection geometries

All logs in native LEVEL units. Real inequalities but
heights are exact integers ≥ 0; can instantiate with chosen odd L. Order of
support exponent etc paid separately. Upper bound h log L pays repeated
prices via pre-L ladder, no power-slop at post-L repeated exponentially.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Scheduling.Weak
open Filter Function RG RG.Supply Bid Lattice Pressure Precision Real Clock Instrument
open scoped Topology

/-- Fixed tests at this stage. Choose `accuracy` genuinely tending to zero
for asymptotic uses. Lower `positive` for the exponent b (B uses b-δ),
`lower` for the fraction in B. Post-L constants; costs already repeated
use `Exchange` chosen before L (including b upper). -/
structure Focus where
  accuracy : ℝ
  positive : ℝ
  lower : ℝ
  funds : Postage
  toll : 0 < accuracy
  pos : 0 < positive
  posL : 0 < lower
  margin : lower ≤ 1

private lemma above (L x : ℝ) (hL : 1<L) (hx : 1 ≤ x) : ∃ i : ℕ, x ≤ L^i ∧ L^i < x*L := by
  let y:= Real.log x/Real.log L
  have hp:=Real.log_pos hL; have ht : 0≤y := div_nonneg (Real.log_nonneg hx) hp.le
  have hv:= Nat.le_ceil y; have hb:=Nat.ceil_lt_add_one ht
  let i:=Nat.ceil y
  have he : 0<x := lt_of_lt_of_le zero_lt_one hx; have hh : 0<L := by linarith
  have hI : 0 < L^i := by positivity
  refine ⟨i, (Real.log_le_log_iff he hI).1 ?_, (Real.log_lt_log_iff hI (by positivity)).1 ?_⟩
  · rw [Real.log_pow]; exact (div_le_iff₀ hp).1 hv
  rw [Real.log_pow,Real.log_mul he.ne' hh.ne']
  apply lt_of_lt_of_le (mul_lt_mul_of_pos_right hb hp)
  unfold y; field_simp; rfl

private lemma underneath (L x : ℝ) (hL : 1<L) (hx : 1 ≤ x) : ∃ i : ℕ, L^i ≤ x ∧ x < L^i*L := by
  let y:= Real.log x / Real.log L
  have hp:=Real.log_pos hL; have ht : 0≤y := div_nonneg (Real.log_nonneg hx) hp.le
  have he:= Nat.floor_le ht; have hh:=Nat.lt_floor_add_one y
  let i:=Nat.floor y
  have hx' : 0<x:=lt_of_lt_of_le zero_lt_one hx; have hL':0<L:= by linarith
  have hi : 0<L^i := by positivity
  refine ⟨i,(Real.log_le_log_iff hi hx').1 ?_,(Real.log_lt_log_iff hx' (by positivity)).1 ?_⟩
  · rw [Real.log_pow]; exact (le_div_iff₀ hp).1 he
  rw [Real.log_mul hi.ne' hL'.ne',Real.log_pow]; have ho := (div_lt_iff₀ hp).1 hh; linarith

/-- A: S index = `u`, cell-side h (plateau exponents). One proof parametric
in every b. Î scale `p^b` not rounded here (round the h required to take
larger seams). -/
structure A (L p M b : ℝ) (u h : ℕ) : Prop where
  le : u ≤ h
  block : p^b*p^ (2:ℕ) ≤ L^u ∧ L^u < p^b*p^ (2:ℕ)*L
  spacing : M^ (10:ℕ) ≤ L^(h-u) ∧ L^(h-u) < M^ (10:ℕ)*L
  log_le : (h:ℝ)*Real.log L ≤ (b+4)*Real.log p

/-- B: largest admissible S index. Use `r=b-δ`, both explicit.
-/
structure B (L p M b r c : ℝ) (u h : ℕ) : Prop where
  le : u ≤ h
  side : L^h ≤ c*p^r ∧ c*p^r < L^h*L
  spacing : M^ (10:ℕ) ≤ L^(h-u) ∧ L^(h-u) < M^ (10:ℕ)*L
  log_le : (h:ℝ)*Real.log L ≤ (b+4)*Real.log p

/-- Produces both heights when additional numeric gates paid. Joint for all
focus requirements; `M` is actual cover, no silently replacing by approximate
s-laws. -/
lemma heights (F : Focus) (p M L b : ℝ) (hp : 1 ≤ p) (hM : 1 ≤ M) (hL : 1<L)
    (hb : 0≤ b) (ha : L^ (2:ℕ)*M^ (10:ℕ) ≤ p^ (2:ℕ)) (he : M^ (10:ℕ)*L ≤ F.lower*p^F.positive) :
    (∃ u h, A L p M b u h) ∧ ∀ r c : ℝ, F.positive ≤ r → r ≤ b → F.lower ≤ c → c ≤ 1 →
      ∃ u h, B L p M b r c u h := by
  have hl : 0<L:= by linarith
  have hm : 0<M:= by linarith
  have hu : 0<p:=by linarith
  have hx h : L^h ≤ p^(b+4) → (h:ℕ)*Real.log L ≤ (b+4)*Real.log p := by
    intro hI; simpa [Real.log_pow, Real.log_rpow hu] using Real.log_le_log (by positivity) hI
  have hh : 1 ≤ M^ (10:ℕ) := one_le_pow₀ hM
  constructor
  · obtain ⟨i,h1,h2⟩ := above L (p^b*p^ (2:ℕ)) hL (one_le_mul_of_one_le_of_one_le (Real.one_le_rpow hp hb) (one_le_pow₀ hp))
    obtain ⟨j,h3,h4⟩:= above L (M^ (10:ℕ)) hL hh
    refine ⟨i,i+j, Nat.le_add_right ..,⟨h1,h2⟩,?_,hx _ ?_⟩
    · simpa using And.intro h3 h4
    calc
      _ ≤ (p^b*p^ (2:ℕ)*L)*(M^ (10:ℕ)*L) := by rw [pow_add]; gcongr
      _ = p^b*p^ (2:ℕ)*(L^ (2:ℕ)*M^ (10:ℕ)) := by ring
      _ ≤ p^b*p^ (2:ℕ)*p^ (2:ℕ) := by gcongr
      _ = _ := by rw [Real.rpow_add hu]; norm_num; ring
  intro r c hc hr hy hz
  have hd := F.posL
  have haC := hd.trans_le hy
  have hm0 : M^ (10:ℕ)*L ≤ c*p^r := he.trans (by gcongr)
  obtain ⟨i,h1,h2⟩:= underneath L (c*p^r) hL (le_trans (one_le_mul_of_one_le_of_one_le hh hL.le) hm0)
  have hv : M^ (10:ℕ) ≤ L^i := le_of_mul_le_mul_right (hm0.trans h2.le) hl
  obtain ⟨j,h3,h4⟩:=underneath L (L^i/M^ (10:ℕ)) hL (by apply (le_div_iff₀ (by positivity)).mpr; simpa)
  have hM10 : 0<M^ (10:ℕ) := by positivity
  have hh' := (le_div_iff₀ hM10).1 h3
  have he' := (div_lt_iff₀ hM10).1 h4
  have hi : j ≤ i := (pow_le_pow_iff_right₀ hL).mp (le_trans (le_mul_of_one_le_right (by positivity) hh) hh')
  have eq : L^i=L^j*L^(i-j) := by rw [← pow_add,Nat.add_sub_of_le hi]
  rw [eq] at hh' he'
  exact ⟨j,i,hi,⟨h1,h2⟩, ⟨le_of_mul_le_mul_left hh' (by positivity),lt_of_mul_lt_mul_left
    (show L^j*L^(i-j) < L^j*(M^ (10:ℕ)*L) by linarith) (by positivity)⟩,hx _ (le_trans h1 <| by
      calc
        _ ≤ 1*p^r := by gcongr
        _ ≤ p^(b+4) := by rw [one_mul]; exact Real.rpow_le_rpow_of_exponent_le hp (by linarith))⟩

variable {G : Gauge} {s : Survey G} {q : Quote} {e : Exchange} {j i : ℕ} {L : ℝ}

/-- Don't use a post-L `p^o(1)` factor raised to h! -/
lemma payment (H : Buy s q e j i L) (h : ℕ) (b p D : ℝ) (hh : (h:ℝ)*Real.log L ≤ (b+4)*Real.log p)
    (hb : b ≤ e.weakHeight) (hp : 1 ≤ p) (hd : 0 ≤ D) (hm : D ≤ e.multiplicity) :
    e.cost^((h:ℝ)*D) ≤ p^(((j:ℝ)+1)⁻¹) := by
  have hX : 0 < Real.log L := Real.log_pos (lt_of_lt_of_le (by norm_num) H.block)
  have hCP := e.ok.2.2.1
  have hC:=Real.log_nonneg hCP
  have hQ:= Real.log_nonneg hp
  let x : ℝ := (j:ℝ)+1; have hx : 0<x:=by unfold x; positivity
  apply (Real.log_le_log_iff (by have := lt_of_lt_of_le zero_lt_one hCP; positivity) (by have := lt_of_lt_of_le zero_lt_one hp; positivity)).1
  rw [Real.log_rpow (by linarith),Real.log_rpow (by linarith)]
  apply le_of_mul_le_mul_right ?_ hX
  have hu := hh.trans (mul_le_mul_of_nonneg_right (add_le_add_left hb _) hQ)
  calc
    _ ≤ ((h:ℝ)*Real.log L)*(e.multiplicity*Real.log e.cost) := by
      have hh := mul_le_mul_of_nonneg_right hm (show 0 ≤ h * Real.log L * Real.log e.cost by positivity); linarith
    _ ≤ ((e.weakHeight+4)*Real.log p)*(e.multiplicity*Real.log e.cost) :=
      mul_le_mul_of_nonneg_right hu (mul_nonneg (hd.trans hm) hC)
    _ ≤ _ := by
      change _ ≤ (x⁻¹*Real.log p)*Real.log L
      have hZ := mul_le_mul_of_nonneg_right H.ladder hQ
      field_simp
      unfold x; linarith
end YM.Next.Scheduling.Weak
