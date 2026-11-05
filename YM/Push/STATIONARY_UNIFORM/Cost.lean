import YM.Next.FOUNDATIONS.SU2
import YM.Push.STATIONARY_UNIFORM.Tame

/-!
# Tables are really pre-L

The exact formulas, with powers/clip etc., are available in Paths. Extra
receipt for checking during pre scheduling: at worst inverse polynomial
radii, polynomial costs, with coefficients and degrees themselves
independent of every continuation at that stage, not just chosen before
using r on some path. This does NOT suffice for pre-buying ALL schedule
needs. Especially this IS polynomial in L, not L-independent value. Does
not claim the constructions of analytic contour kernels/loops/cubic-output
path coeffs at a particular adequate width. Keep this rate from constraining
their pre-L recurrence without more work.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Uniform
open Lattice Wilson RG Precision Tree Pressure Gauge Exterior Bid Work.F01
open Filter Function Set Metric
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators InnerProductSpace Classical

variable (G : Gauge) {C Z r μ M W a K : ℝ} {j n : ℕ} {f g : Patch → ℝ}

lemma tame_compose (hf : Tame j f) (hg : Tame j g) (n : ℕ) : Tame j (fun x => composeCost n (f x) (g x)) :=
  ((tame_k _).mul hf).mul (((tame_k _).add hg).power _)
lemma tame_travel {u : Patch → ℕ} (hf : Tame j (fun x => (u x:ℝ))) (C : ℝ) (n : ℕ) : Tame j (fun x => travelCost G n (u x) C) :=
  tame_compose ((tame_k _).mul (((tame_k _).add ((tame_k _).mul ((tame_k _).add hf))).power _)) (tame_k _) _
lemma tame_price (h : Tame j f) : Tame j (fun x => priceCost G (f x)) := (tame_k _).add ((tame_k _).mul h)
lemma tame_frames (j : ℕ) (K C : ℝ) (n : ℕ) : Tame j (fun x => scoreCost x G n K C) := by
  have hx : Tame j (fun x : Patch => ((8*x.radius:ℕ):ℝ)) := by
    simp_rw [Nat.cast_mul]; exact (tame_k _).mul (tame_radius j)
  have he := tame_travel G (u:=fun x => 8*x.radius) hx (composeCost n C 1) n
  exact tame_price G (((tame_k _).mul ((tame_k _).mul he)).mul (tame_k _))
lemma lit_points (j : ℕ) : Lit j points := by
  have he : points = fun P => (↑P.radius+↑P.radius+1:ℝ)^4 := by funext; rw [points_cost]; push_cast; rfl
  exact {
    pos := fun x _ => points_pos _
    high := he.symm ▸ (((tame_radius j).add (tame_radius j)).add (tame_k _)).power _
    low := (tame_k 1).ltMore (fun x _ => by
      rw [abs_of_pos (inv_pos.mpr (points_pos x))]; exact inv_le_one_of_one_le₀ (points_ge _)) }
lemma lit_gap (j : ℕ) : Lit j rootGap :=
  (lit_k (show 0<(2:ℝ) by norm_num)).mul ((lit_points j).inv.pow 2)
lemma lit_score (he : ExpReceipt G n K) (C : ℝ) (h : 0≤C) (j : ℕ) : Lit j (fun x => hilbertRadius x G n K C) := by
  refine (lit_k one_pos).min' ((lit_gap j).div ((lit_k (show (0:ℝ)<2 by norm_num)).mul ((lit_k one_pos).add_left (tame_frames G _ _ _ _) (fun x _ => ?_))))
  have hK := (he 0 (by simp)).nonneg
  unfold scoreCost
  apply le_trans zero_le_one (show 1 ≤ priceCost G _ from ?_)
  apply le_add_of_nonneg_right
  unfold travelCost composeCost
  positivity
lemma positive_frame (h : ExpReceipt G n K) {D δ : ℝ} (he : LogReceipt G D δ) (Q : KernelChoices) (hC : 0≤C) (j : ℕ) :
    Lit j (fun x => frameRadius x G n K C D δ Q) := by
  have hf : Lit j (fun x : Patch => Inputs.pathChange G x C) := (lit_k one_pos).add_left
    (((tame_k _).mul (tame_radius j)).mul (tame_k _)) (fun x _ => by
      unfold Inputs.variation; have := G.colorScale_pos; positivity)
  have ha : Lit j alignCost := (lit_k one_pos).add_left (((lit_points j).high.power _).mul (tame_k _)) (fun x _ => by positivity)
  have hw := lit_score G h C hC j
  have hM := ha.mul hf
  exact hw.min' (((lit_k Q.frame_cut_pos).div ((lit_k (show (0:ℝ)<3 by norm_num)).mul hf)).min'
    (((lit_k he.2.1).div hM).min' (hw.div (((lit_points j).mul (lit_k he.1)).mul hM))))
lemma positive_prediction (h : ExpReceipt G (n+1) K) {D δ W : ℝ} (he : LogReceipt G D δ) (Q : KernelChoices)
    (hv : FocusReceipt G n W r) (hC : 0≤C) (j : ℕ) : Lit j (fun x => predictionRadius x G Q n K C D δ r) := by
  have hf : Lit j (fun x : Patch => Inputs.pathChange G x C) := (lit_k one_pos).add_left
    (((tame_k _).mul (tame_radius j)).mul (tame_k _)) (fun x _ => by
      unfold Inputs.variation; have := G.colorScale_pos; positivity)
  have ha : Lit j alignCost := (lit_k one_pos).add_left (((lit_points j).high.power _).mul (tame_k _)) (fun x _ => by positivity)
  have hz : Lit j (fun x => connectorMove x G C) :=
    ((lit_k (show (0:ℝ)<2 by norm_num)).mul (ha.mul hf)).add_left (lit_size.high.mul (tame_k _)) (fun x _ =>
        mul_nonneg (by positivity) (div_nonneg hC G.colorScale_pos.le))
  refine (positive_frame G h he Q hC j).min' ?_
  exact ((lit_k (Real.sqrt_pos.mpr Q.predictor_cut_pos)).div hz).min'
    ((lit_k hv.1).div ((lit_k G.colorScale_pos).mul hz))

lemma tame_implicit (hf : Tame j f) (hg : Tame j g) (n : ℕ) : Tame j (fun x => implicitCost 1 (f x) (g x) n) := by
  induction n with
  | zero => exact tame_k 1
  | succ n ih => exact ih.add (hg.mul (hf.add (((tame_k _).mul hf).mul (((tame_k _).add ih).power _))))
lemma tame_connector (j : ℕ) (K C : ℝ) (n : ℕ) : Tame j (fun x => connectorCost x G n K C) := by
  have hf : Tame j (fun x => hatsCost x G n K C) :=
    tame_compose (tame_k _) (tame_implicit (tame_frames G j K C (n+1)) ((lit_gap j).div (lit_k (show (0:ℝ)<2 by norm_num))).low _) _
  have ht := tame_travel G (u:=fun x=>x.L.val) (j:=j) lit_size.high C n
  exact ((tame_k _).mul (((tame_k _).mul hf).mul ht)).mul hf
lemma tame_macro (j : ℕ) : Tame j (fun x => macroR x) := by
  unfold macroR; simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]; exact (tame_radius j).add ((tame_k _).mul lit_size.high)
lemma lit_zeroGap (p : Clip) (Q : KernelChoices) (K C : ℝ) (j : ℕ) : Lit j (fun x => zeroGap x Q p K C) := by
  have hS : Tame j (fun x => ((Fintype.card (Site x.L)):ℝ)) := by
    suffices H : Tame j (fun x => (x.L.val:ℝ)^4) by simpa [Site,Per,Axis] using H
    exact lit_size.high.power _
  have hT : Tame j (fun x => ((box (macroR x)).card:ℝ)) := by
    simp_rw [Corona.box_size,Nat.cast_pow,Nat.cast_add,Nat.cast_one]; exact (((tame_macro j).add (tame_macro j)).add (tame_k _)).power _
  have hL : Tame j (fun x => linkCost Q K C x.L) := by
    unfold linkCost; simp_rw [div_eq_mul_inv]
    have hP : Tame j (fun x => C*(x.L.val:ℝ)) := (tame_k _).mul lit_size.high -- D slot
    have hM : Tame j (fun x => K*(x.L.val:ℝ)^2) := (tame_k _).mul (lit_size.high.power _)
    exact ((((tame_k _).mul lit_size.high).add (tame_k _)).mul hP).add ((hM.add ((tame_k _).mul (lit_size.pow 2).low)).add hM)
  have hh : Tame j (fun x => curlFactor x.L (box (macroR x)) (linkCost Q K C x.L)) :=
    (((((tame_k _).mul (hL.power _)).mul hS).mul (tame_k _)).mul (hT.mul (tame_k _))).mul hT
  exact (lit_k (lt_min (spoke_pos p) Q.penalty_pos)).div (((lit_k one_pos).add_left hh
    (fun x _ => by unfold curlFactor; positivity)).add_left ((tame_k _).mul hS)
    (fun x _ => show 0 ≤ probeFactor x.L by unfold probeFactor; positivity))

lemma Lit.count (h : Lit j f) (hr : ∀ x : Patch, x.J=j → f x ≤ r) : Tame j (fun x => countCost (f x)) :=
  (((Tame.exp' (C:=r*2) (fun x hx => mul_le_mul_of_nonneg_right (hr x hx) (by norm_num))).mul (tame_k _)).mul
    (h.pow 6).low).mul (tame_k _)

lemma entry_top (hm : 0<μ) (n j : ℕ) : Lit j (fun x => entryWidth n x.L μ) ∧
    ∀ x : Patch, x.J=j → entryWidth n x.L μ ≤ μ := by
  refine ⟨(lit_k hm).div ((lit_k (show (0:ℝ)<4*((n:ℝ)+1) by positivity)).mul ((lit_k one_pos).add lit_size)),fun x _ => div_le_self hm.le ?_⟩
  calc
    (1:ℝ) ≤ 4* (1:ℝ)*1 := by norm_num
    _ ≤ 4*(↑n+1)*(1+(x.L.val:ℝ)) := by
      gcongr
      · exact le_add_of_nonneg_left (by positivity)
      exact le_add_of_nonneg_right (by positivity)

lemma tame_quad (p : Clip) (Z Z' C : ℝ) (hm : 0<μ) (j n : ℕ) : Tame j (fun x => quadCost G n Z Z' μ C p x.L) := by
  apply Tame.add _ (tame_k _)
  apply (tame_k _).mul
  apply Tame.exp' (C:=μ*(n:ℝ)*(5+1))
  intro x _
  unfold entryWidth signedCost; push_cast
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity : 0 < 4*((n:ℝ)+1)*(1+(x.L.val:ℝ)))]
  apply le_trans (mul_le_mul_of_nonneg_left (show (n:ℝ)*(5+(x.L.val:ℝ)) ≤ n*(5+1)*(4*((n:ℝ)+1)*(1+(x.L.val:ℝ))) from ?_) hm.le)
  · exact le_of_eq (by ring)
  have hl : 0 ≤ (n:ℝ) := by positivity
  have hh : 0 ≤ (x.L.val:ℝ) := by positivity
  have hv : 0 ≤ (n:ℝ)*(x.L.val:ℝ) := by positivity
  have hu : 0 ≤ (n:ℝ)*n*(x.L.val:ℝ) := by positivity
  nlinarith

lemma Lit.count2 (h : Lit j f) (he : ∀ x : Patch, x.J=j → f x ≤ r) (k : ℕ) : Tame j (fun x => k * countCost (f x/2)) :=
  (tame_k _).mul ((h.div (lit_k (show (0:ℝ)<2 by norm_num))).count (fun x hx => div_le_div_of_nonneg_right (he x hx) (show (0:ℝ)≤2 by norm_num)))

lemma tame_noise (Z K W : ℝ) (hm : 0<μ) (j n : ℕ) : Tame j (fun x => noiseEntry G n Z K W μ x) := by
  refine (tame_price G ((tame_k _).mul (tame_compose (tame_k _) (tame_connector G j K (fineCost G (n+1) Z) n) n))).mul ?_
  let a : ℝ := 1+16*(j+3:ℝ)+2
  apply Tame.exp' (C:=μ*n*a)
  intro x hx
  have he : (noiseCost x:ℝ) = (x.L.val:ℝ) * a := by unfold noiseCost Patch.radius a; push_cast; rw [hx]; ring
  rw [Nat.cast_mul, he]; unfold entryWidth
  have hv : entryWidth n x.L μ * x.L.val ≤ μ := by
    unfold entryWidth; rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity : 0<4*((n:ℝ)+1)*(1+(x.L.val:ℝ)))]
    apply mul_le_mul_of_nonneg_left _ hm.le
    have hh : 0≤(n:ℝ)*(x.L.val:ℝ) := by positivity
    have hz : 0≤(n:ℝ) := by positivity
    have hr : 0≤(x.L.val:ℝ) := by positivity
    linarith
  apply le_trans (le_of_eq (show _=(entryWidth n x.L μ*x.L.val) * ((n:ℝ)*a) from ?_))
    ((mul_le_mul_of_nonneg_right hv (mul_nonneg (by positivity) (by unfold a; positivity))).trans_eq (by ring))
  unfold entryWidth; ring

lemma lit_all (Q : KernelChoices) (p : Clip) (Z Z' C K W : ℝ) (hm : 0<μ) (n j : ℕ) :
    Lit j (fun x => allCost G n Z Z' μ C K W p x Q) := by
  obtain ⟨hh,hc⟩ := entry_top hm n j
  have he : Tame j (fun x : Patch => countCost (entryWidth n x.L μ/2)) := by simpa only [Nat.cast_one,one_mul] using hh.count2 hc 1
  have ht := tame_quad G p Z Z' C hm j n
  refine (lit_k one_pos).add_left (Tame.absolute ?_) (fun x _ => abs_nonneg _)
  refine (Tame.mul ?_ he).add ((tame_k _).mul (((tame_noise G Z K W hm j n).mul (tame_k _)).mul he))
  exact ((((tame_k _).mul ht).add (tame_k _)).add (tame_k _))

lemma lit_tilt {Z : Patch → ℝ} (h : Lit j f) (hp : Lit j g) (he : Lit j Z) (heZ : ∀ x : Patch,x.J=j → g x ≤ M) (K : ℕ) :
    Lit j (fun x => tiltWidth K (f x) (g x) (Z x)) := by
  refine (hp.div (lit_k (show (0:ℝ)<4 by norm_num))).min'
    (h.div ((lit_k (show (0:ℝ)<2 by norm_num)).mul ((lit_k one_pos).add_left ?_ ?_)))
  · exact (he.mul ((lit_k (show (0:ℝ)<4 by norm_num)).div hp)).high.mul (hp.count2 heZ K)
  intro x hx; have hz:= he.pos x hx; have hr:=hp.pos x hx
  exact mul_nonneg (show 0 ≤ Z x*(4/g x) by positivity) (mul_nonneg (Nat.cast_nonneg _) (count_pos (half_pos hr)).le)

/-- Even the inverse estimate's rate based on torus growth etc. carries only
these powers. -/
theorem Before.power {μ C : ℝ} {Q : KernelChoices} {j n : ℕ} (A : Before G μ C j Q n) (hm : 0<μ) (p : Clip) :
    let F := A.tables p
    Lit j (fun x => (F x).value) ∧ Lit j (fun x => (F x).width) ∧ Lit j (fun x => (F x).rate) ∧
    Lit j (fun x => (F x).initial) ∧ Lit j (fun x => (F x).gap) ∧ Lit j (fun x => (F x).safety) ∧
    Lit j (fun x => (F x).inverse) ∧ Lit j (fun x => (F x).zone) ∧ Lit j (fun x => (F x).horizon) := by
  intro F
  obtain ⟨hh,hc⟩ := entry_top hm n j
  have hv : Lit j (fun x => (F x).value) := lit_all G Q p A.Z A.X C A.lc A.W hm n j
  have hw : Lit j (fun x => (F x).width) := hh.div (lit_k (show (0:ℝ)< 2*((n:ℝ)+1) by positivity))
  have hR : Lit j (fun x => (F x).initial) := positive_prediction G A.exp A.log Q A.focus (fine_pos A.labels) j
  have hg : Lit j (fun x => (F x).gap) := lit_zeroGap p Q A.c₁ A.c₂ j
  let M := weaker n μ
  have ht x (hx : x.J=j) : (F x).width ≤ M := div_le_div_of_nonneg_right (hc x hx) (by positivity)
  let K := townCost G
  have he : Lit j (fun x => (F x).rate) := lit_tilt (hg.div (lit_k (show (0:ℝ)<2 by norm_num))) hw hv ht K
  let N (x) := (K:ℝ)*countCost (F x).width
  let u x := (F x).value * N x; let v x := (F x).value * (N x)^2
  have hN : Tame j N := (tame_k _).mul (hw.count ht)
  have hD x (hx : x.J=j) : 0 ≤ N x := mul_nonneg (by positivity) (count_pos (hw.pos _ hx)).le
  have hu : Lit j (fun x => 1+u x) := (lit_k one_pos).add_left (hv.high.mul hN) (fun x hx => mul_nonneg (hv.pos _ hx).le (hD _ hx))
  have hJ : Tame j v := hv.high.mul (hN.power _)
  have hV x (hx : x.J=j) : 0 ≤ v x := mul_nonneg (hv.pos _ hx).le (sq_nonneg _)
  have hs : Lit j (fun x => (F x).safety) := (hR.div (lit_k (show (0:ℝ)<2 by norm_num))).min'
    (hg.div ((lit_k (show (0:ℝ)<2 by norm_num)).mul ((lit_k one_pos).add_left hJ hV)))
  let W x := (F x).gap/2/2
  have hhW : Lit j W := (hg.div (lit_k (show (0:ℝ)<2 by norm_num))).div (lit_k (show (0:ℝ)<2 by norm_num))
  have hE : Tame j (fun x => countCost (F x).rate) := he.count (r:=M/4) (fun x hx => le_trans
    (show (F x).rate ≤ (F x).width/4 from min_le_left ..)
    (div_le_div_of_nonneg_right (ht _ hx) (by norm_num)))
  have hI : Lit j (fun x => (F x).inverse) := (lit_k one_pos).add_left
    (hhW.low.mul ((tame_k K).mul hE)) (fun x hx => mul_nonneg (inv_pos.mpr (hhW.pos _ hx)).le (mul_nonneg (Nat.cast_nonneg _) (count_pos (he.pos _ hx)).le))
  have hd : Lit j (fun x => 4*(F x).inverse) := (lit_k (show (0:ℝ)<4 by norm_num)).mul hI
  have hl : Lit j (fun x => (F x).zone) := hs.min'
    ((lit_k (show (0:ℝ)<1 from one_pos)).div (hd.mul ((lit_k one_pos).add_left hJ hV)))
  exact ⟨hv,hw,he,hR,hg,hs,hI,hl,hl.min' (hl.div (hd.mul hu))⟩
end YM.Push.Uniform
