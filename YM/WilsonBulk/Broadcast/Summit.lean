import YM.WilsonBulk.Broadcast.Rainy
import YM.WilsonBulk.Trees.Pressure

/-!
# Full leading kinetic precision for `Text` collection. Unit normalization
  target proved elsewhere; this file pins readout on analytic widths. Keep
  structural representation self-contained independent of ANY gauge spin.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk.Parapet
open scoped Topology Classical BigOperators ENNReal ContDiff Matrix.Norms.Frobenius
open Lattice Laurent Filter Equiv Function Bloch Matrix Precision Stationary Audience Exterior Wilson
open Work.F08 RG Sheet Pert.Bulk Atelier
variable {α β : Type} {p q σ : ℝ} {c : Side} {G : Gauge} {P : Patch} {B V : Bed}

-- record isolated ranks
def usher (e i : ℕ) (v : Page α i) : Record α := fun d n=> if d=e then if h:n=i then escort (finCongr h.symm) v else 0 else 0
lemma usher_at (i e : ℕ) (v : Page α i) : usher e i v e i = v := by rw [usher,if_pos rfl,dif_pos rfl]; rfl
lemma usher_else (i j e d : ℕ) (v : Page α i) (h : i≠j ∨ d≠e) : usher e i v d j=0 := by
  rcases h with h|h; · simp [usher,Ne.symm h]
  exact if_neg h
lemma usher_ko (i e : ℕ) (x : Text α i) (p : Pamphlet (usher e i x)) : Public x := by rw [← usher_at i e x]; exact p .. --.. guard
-- around tungsten leading page, sym always done
def tungsten (G : Gauge) (B : Bed) := stillColor G (actionKernel B.metric)
def onTop (G : Gauge) (B : Bed) := polish ((1/2:ℝ) • pair (plain (tungsten G B)))
def summit (G : Gauge) (B : Bed) := usher 0 2 (onTop G B)
lemma summit_style (G : Gauge) (B : Bed) : Document (summit G B) := ⟨fun e i h=> usher_else _ _ _ _ _ (by omega),fun e i=> by
    by_cases h:i=2 ∧ e=0; swap; · rw [summit,usher_else (v:=onTop G B) _ _ _ _ (by omega)]; exact Regular.zero
    obtain ⟨rfl,rfl⟩:= h; rw [summit,usher_at]; exact polish_ready _,fun i j h=> usher_else _ _ _ _ _ (by omega)⟩ -- usher args order
lemma summit_hairless (G : Gauge) (B : Bed) : Cashless (summit G B) := fun e=> usher_else _ _ _ _ _ (by omega)
lemma tungsten_cost (G : Gauge) (hp : (actionKernel B.metric).strip σ p) : (tungsten G B).strip σ p := by
  apply painted_strip _ _ _ _ hp
  exact Push.AbsoluteSums.budget_nonneg (hp (coord 0) (coord 0)) -- check
lemma tungsten_delta (h : (minusRows (actionKernel B.metric) (actionKernel V.metric)).strip σ p) : (minusRows (tungsten G B) (tungsten G V)).strip σ p := by
  rw [show minusRows (tungsten G B) (tungsten G V)= stillColor G (minusRows (actionKernel B.metric) (actionKernel V.metric)) from ?_]; apply painted_strip _ _ _ _ h
  · exact Push.AbsoluteSums.budget_nonneg (h (coord 0) (coord 0))
  ext1 i; ext1 j; ext1 z; unfold tungsten stillColor painted minusRows; split <;> simp_all
abbrev oxidize (G : Gauge) (p : ℝ) : ℝ:= |(1/2:ℝ)| * (Fintype.card (Cloth G)*p)
lemma onTop_cost (G : Gauge) (hp : (actionKernel B.metric).strip σ p) : Within (lawn (Cloth G)) σ (oxidize G p) (onTop G B) := ((lawn_pair (tungsten_cost G hp) (Push.AbsoluteSums.budget_nonneg (hp (coord 0) (coord 0)))).scale _).clean
lemma onTop_price (B : Bed) (G : Gauge) : Pervasive (onTop G B) := ((Pervasive.plain_pair _).scale _).polished
lemma summit_public (G : Gauge) (hp : (actionKernel B.metric).strip σ p) (he : 0<σ) : Pamphlet (summit G B) := fun i j=> by
  by_cases h:i=0 ∧ j=2; swap; · rw [summit,usher_else]; exact Public.zero; omega
  obtain ⟨rfl,rfl⟩:= h; rw [summit,usher_at]; exact ⟨onTop_price B G, ⟨σ,oxidize G p, he,onTop_cost G hp⟩⟩
lemma summit_T (G : Gauge) (hv : 0 ≤ σ) (h : B.metric.strip σ p) : coupon c 2 (onTop G B) = polish ((1/2:ℝ) • pair (fun i j=> matrixK G c B i j)) := by
  have hh : matrixK G c B=(tungsten G B).acts c := by rw [matrixK,tungsten, see_stillColor, actionKernel_acts hv h]
  have hz := actionKernel_strip hv h
  rw [hh]; exact (coupon_reads c (onTop_price B G)).uniq (((plain_orates (tungsten G B)).scale (1/2:ℝ)).polished ((lawn_pair (tungsten_cost G hz) (Push.AbsoluteSums.budget_nonneg (hz (coord 0) (coord 0)))).scale (1/2:ℝ)) hv) (small_onto _ _) (by omega)
lemma onTop_delta (B V : Bed) (h : (minusRows (actionKernel B.metric) (actionKernel V.metric)).strip σ p) : Within (lawn (Cloth G)) σ (oxidize G p) (onTop G B-onTop G V) := by
  unfold onTop; rw [← polish_minus, ← smul_sub,show pair _-pair _= pair (plain (minusRows (tungsten G B) (tungsten G V))) from rfl]; exact ((lawn_pair (tungsten_delta h) (Push.AbsoluteSums.budget_nonneg (h (coord 0) (coord 0)))).scale _).clean

lemma force_script [Fintype α] (V : Matrix α α ℝ) : script (pair (fun i j=> V i j)) = furrow V MvPolynomial.X (MvPolynomial.X (R:=ℝ)) := by
  rw [script]; unfold furrow knot; rw [typeset_fin_hitch]; refine Finset.sum_congr rfl fun i _=>?_
  rw [typeset_fin_hitch]; unfold quill; rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _=>?_
  simp only [Fintype.sum_unique, field_hitch,pair,hitch_zero, ← MvPolynomial.C_mul'] -- inspect
  change MvPolynomial.C (V i j) * (MvPolynomial.X i * (MvPolynomial.X j*field (default:Legs α 0)))=_
  rw [field,Fin.prod_univ_zero]; ring
lemma grains_root [Fintype α] (V : Matrix α α ℝ) : grains V=PowerSeries.C (forceQ V MvPolynomial.X) := (forceQ_map V MvPolynomial.X (post (Formula α))).symm -- inference
lemma summit_tape (G : Gauge) (hv : 0 ≤ σ) (h : B.metric.strip σ p) (n : Side) : volumeTape (issue n (summit G B))= grains (matrixK G n B) := by
  ext1 i; rw [grains_root,PowerSeries.coeff_C,tape_power,capsule]; cases i with
  | zero => rw [Finset.sum_eq_single 2, if_pos rfl,Sheet.issue,summit, usher_at, summit_T G hv h] -- issue & usher
            · simp only [script_polish,script_scale,force_script]
            · intro i _ hi; unfold Sheet.issue summit; rw [usher_else, coupon_zero, script_zero]; omega
            simp [allowed]
  | succ k=> rw [if_neg (by omega)]; exact Finset.sum_eq_zero fun i _=> by unfold Sheet.issue summit; rw [usher_else, coupon_zero, script_zero]; omega
end YM.WilsonBulk.Parapet
