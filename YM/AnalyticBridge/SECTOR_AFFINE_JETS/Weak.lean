import Mathlib.Analysis.Fourier.Convolution
import YM.Next.BOUNDARY.Coordinates
import YM.Next.FREE_KERNELS.Signal
import YM.Next.ROTATIONS.Response
import YM.Next.SCHEDULE.Blocks
import YM.Next.SCHEDULE.GridCost
import YM.Next.SCHEDULE.Postal
import YM.Push.CUTOFF_PROJECTORS.Along
import YM.Push.FREE_RESOLVENT.JetWindows
import YM.Push.FREE_RESOLVENT.Torus
import YM.Push.STATIONARY_UNIFORM.Beacons
import YM.Push.STATIONARY_UNIFORM.Travel
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Patch
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Stencils



/-!
# Real resources near selected affine rows

On V with exact flags. Two default resource needs beyond covariance: actually
show all used v,w columns agree with their unclipped output good m' extension
AND their unmasked/path values are small at the evaluation point. Use only
weak gauges on each fixed-size box. No realizability of fine defaults, no
indicator differentiation; inequalities authorize at equality too. Keep the
older `mask` proofs for subsequent push comparisons.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.SectorAffine.Offset

open Filter Function Lattice Wilson RG Precision Pressure Tree Exterior Bloch
open YM.Next YM.Next.Fluctuations YM.Next.SectorChange YM.Next.SectorChange.Rows
open YM.FreeResolvent (Mark Bundle native Cost)
open YM.FreeResolvent.TestD
open YM.Push.Uniform (bolt Allows Requests travelCost)
open YM.Push.SectorMeasure YM.Push.SectorMeasure.Oriented
open YM.Work
open Pressure.Tube
open scoped Topology ContDiff BigOperators InnerProductSpace Classical Matrix.Norms.Frobenius

variable {G : Gauge} {c f : Side} {R k n L : ℕ} {C M s σ d t x r κ : ℝ} {p : Site f → Site c} {S : StepData c f} {A : Stores S} {F : Forest S.ratio} {o : Signed}

/-- Weak `D'` branch on every coarse face through the fixed tape
center. No assumption that the criteria using s.act on negative-oriented
inputs preserve shots. -/
def secure (x : ℝ) (r : ℕ) (i : Site c) (V : Config G c) :=
  ∀ p : Cell c, separation i p.1 ≤ r → toll V p ≤ temp x

lemma guard (V : Config G c) (hp : A.flags=RG.flags (temp x) V)
    (i : Where S) (o : Signed) (h : span S.patch x ≤ radiusB x/50)
    (ht : curb (shots S x) A F x o i) : secure x (radiusB x) (roots S i) (pull o 0 V) := by
  intro p he; by_contra! hx
  let B := pull o 0 V
  have hf : affine o 0 p.1 ∈ A.flags := by
    rw [hp, ← H03.flags_send o 0]
    apply Finset.mem_image_of_mem
    exact (flags_spec ..).2 ⟨p,E01.base_touched _,hx⟩
  simp only [affine,add_zero] at hf
  apply (guarded h ht).1
  refine halo_spec.mpr ⟨_,Finset.mem_union_right _ hf,?_⟩; rw [separation_signed,separation_comm]; omega

lemma kept_vision {P : Teller G} {T : Tube G S} (hT : P.Funds S T)
    (h : Stores.till x+1 ≤ radiusB x/50 ∧
      ∀ k : ℕ, temp x * Real.exp (k/P.below.clip.relaxation) < 2 → k+1 ≤ radiusB x/50)
    (V : Config G c) (i : Site c) (y : Twin c) (hs : secure x (radiusB x) i V)
    (hv : separation i y.1.1 ≤ radiusB x/50) :
    T.vision (Stores.till x) (temp x) V y=T.Xn (Stores.till x) V y := by
  unfold vision Xn plotted thinned; split
  · rw [if_pos ?_]; intro q
    by_contra! hk
    have ht := h.2 (separation y.1.1 q.1) (by rw [← hT.low]; exact hk.trans_le (G.chord_le_two _))
    apply hk.not_ge
    have hj := separation_triangle i y.1.1 q.1
    apply (hs q (by omega)).trans
    refine le_mul_of_one_le_right (temp_nonneg x) (Real.one_le_exp ?_); have := T.low.radius_pos; positivity
  split
  next he => simp
  next he =>
    have hf : 0<toll V y.1 := lt_of_le_of_ne (G.chord_nonneg _) (Ne.symm he)
    rw [min_eq_left ((le_div_iff₀ hf).mpr (by rw [one_mul]; exact hs _ (by omega))),one_smul]

section allowance

-- exact support, even for wrapping arcs. Could reuse E03 Anchored with /50.
lemma leap_bound {T : Tube G S} (V : Config G c) (i : Twin f) (j : Twin c) :
    ¬separation (S.ratio.parent i.1.1) j.1.1 ≤ Stores.till x → T.Φ (Stores.till x) V i j=0 := by
  intro h
  have hf (u : Cover) : casted S T.R (Stores.till x) V (mesh i) (mesh j) u=0 := by
    unfold casted; dsimp only
    split
    next ht =>
      let w := route (lift (S.ratio.residue (mesh i).1)) (S.patch.L.val • u) 1
      have he := E03.sep_walk _ (E03.parent_step S) (mesh i).1 w
      rw [show stop (mesh i).1 w=_ from E03.casted_endpoint S (mesh i).1 u,S.ratio.embed_parent,← ht.2] at he
      exact (h (he.trans ht.1)).elim
    rfl
  simp [Φ,leap,hf]

lemma kick_bound {T : Tube G S} (V : Config G c) (i : Bond c) (j : Twin c) :
    ¬separation i.1 j.1.1 ≤ Stores.till x → T.Φ' (Stores.till x) V i j=0 := by
  intro h
  let B := fun u => priced (Stores.till x) S.patch.L.val V T.R.mn (pole i) (mesh j) u
  change (∑' u, B u) = 0
  have hf (u : Cover) : B u=0 := by
    unfold B priced; split
    next ht =>
      let w := route 0 u 1
      have he := E03.sep_walk id (fun i j => E03.sep_step i j) (pole i).1 w
      have hh : stop (pole i).1 w=(mesh j).1 := by
        rw [ht.2]; simpa only [map_zero,add_zero] using E03.stop_route (pole i).1 0 u
      rw [hh] at he
      exact (h (he.trans ((le_mul_of_one_le_right (Nat.zero_le _) S.patch.L.property).trans ht.1))).elim
    rfl
  simp_rw [hf]; rw [tsum_zero]
end allowance

private lemma secured_flag (G : Gauge) (V : Config G c) {i : Site c}
    (h : secure x n i V) (y : Site c) (R : ℕ) (he : separation i y+(R+1) ≤ n) (hp : 2*(R+1)<c.val) :
    let C := 16*(2*((R+1:ℕ):ℝ)+1)^5*(Fintype.card PlaqAxes:ℝ)
    ∃ w : Site c → G.El,
    (∀ p : Bond c, separation y p.1≤R → G.chord (Lattice.gauge w V p) ≤ C*temp x) ∧
    ∀ i : Bond f, separation y (S.ratio.parent i.1) ≤ R → G.chord (Lattice.gauge (constantGauge w S.ratio) (replica S.ratio V) i) ≤ C*temp x := by
  intro C
  obtain ⟨w, hw⟩ := E08.axial_patch y V R (R+1) (by omega) hp (temp x) (temp_nonneg x)
    (fun z hz p => h (z,p) ((separation_triangle i y _).trans ((Nat.add_le_add_left hz _).trans he)))
  refine ⟨w,hw,fun b hb => ?_⟩
  rw [copied S.ratio S.patch.odd_side]; unfold replica; split
  · rw [G.chord_one]; exact mul_nonneg (by unfold C; positivity) (temp_nonneg _)
  exact hw _ hb

lemma secure_faces (P : Patch) (G : Gauge) : ∃ D : ℝ, 0<D ∧ ∀ᶠ x : ℝ in atTop,
    ∀ {c f : Side} (S : StepData c f), S.patch=P → 100*(1+radiusB x) ≤ c.val →
    ∀ (i : Site c) (V : Config G c), secure x (radiusB x) i V →
    ∀ p : Cell f, separation i (S.ratio.parent p.1) ≤ Stores.till x →
      toll (replica S.ratio V) p ≤ D*temp x := by
  let D := 16*(2*(5:ℝ)+1)^5 * (Fintype.card PlaqAxes:ℝ)
  have hd : 0<D := by
    unfold D
    have h : 0<Fintype.card PlaqAxes := by letI : Nonempty PlaqAxes := ⟨⟨(0,1),by decide⟩⟩; exact Fintype.card_pos
    positivity
  refine ⟨4*D, by positivity,?_⟩
  filter_upwards [Work.E01.radiusB_tendsto.eventually_ge_atTop 100] with x hx
  intro c f S hP hF i V h b hb
  obtain ⟨w,-,ht⟩ := secured_flag (S:=S) G V h (S.ratio.parent b.1) 4 (by unfold Stores.till at hb; omega) (by omega)
  let U := replica S.ratio V; let p := constantGauge w S.ratio
  let u := Lattice.gauge p U; let W (i : Bond f) := if separation (S.ratio.parent b.1) (S.ratio.parent i.1) ≤ 4 then u i else (1:G.El)
  rw [← toll_gauge p]; unfold toll faceValue; rw [travel_near S.ratio.parent (E03.parent_step S) _ W _ _ 4 (le_refl _) ?_]
  · have hx (i : Bond f) : G.chord (W i) ≤ D*temp x := by
      unfold W; split
      next hi => exact (ht _ hi).trans_eq (by unfold D; norm_num)
      rw [G.chord_one]; exact mul_nonneg hd.le (temp_nonneg x)
    apply (travel_chord W _ _ _ hx).trans_eq; simp [square,mul_assoc]
  exact fun i hi => (if_pos hi).symm

lemma z_turn (G : Gauge) (V Q : Config G c) (i : Bond c) (w : Site c → G.El) :
    Z S (Lattice.gauge w Q) (Lattice.gauge w V) i = G.adjoint (w i.1) (Z S Q V i) := by
  unfold Z Lattice.gauge; rw [map_smul,← G.curvature_conjugate]; congr 2; group

lemma secure_noise (G : Gauge) (P : Patch) (K : KernelChoices) (hk : P.Branches K G) :
    ∃ D : ℝ, 0<D ∧ ∀ᶠ x : ℝ in atTop,
    ∀ {c f : Side} (S : StepData c f), S.patch=P → S.kernel=K → 100*(1+radiusB x) ≤ c.val →
    ∀ (i : Bond c) (V : Config G c), secure x (radiusB x) i.1 V → ∀ k : S.Choices,
      ‖Z S (S.prediction (replica S.ratio V) k) V i‖ ≤ D*temp x := by
  let L := LocalJet.allot P; let M := LocalJet.permit P
  obtain ⟨A,δ,hA,hδ,hE⟩ := extend_interior G
  obtain ⟨C,r,hC,hr,h⟩ := z_chart_cost P K G hk
  let t := A*M; let D := (C*(1+r))*t
  have hL : predReach P ≤ L := by unfold L LocalJet.allot; omega
  have hm : 0<M := by
    unfold M LocalJet.permit
    have hp : 0<Fintype.card PlaqAxes := by letI : Nonempty PlaqAxes := ⟨⟨(0,1),by decide⟩⟩; exact Fintype.card_pos
    positivity
  refine ⟨D, by unfold D t; positivity,?_⟩
  have he {D r : ℝ} (hr : 0<r) : ∀ᶠ x : ℝ in atTop, D*temp x ≤ r := by
    filter_upwards [E01.fiery_le G 1 D,(E01.largeT_tendsto G 1).eventually (ge_mem_nhds hr)] with x hx he
    simpa [fiery,betaF] using hx.trans he
  filter_upwards [he (D:=M) hδ, he (D:=t) hr, Work.E01.radiusB_tendsto.eventually_ge_atTop (L+1)] with x hx hx' ht
  intro c f S hP hK hF i V hX k
  have hS : S.patch.Branches S.kernel G := by rw [hP,hK]; exact hk
  obtain ⟨w,hu,hv⟩ := secured_flag (S:=S) _ V hX i.1 L (by simp [ht]) (by omega)
  let U := replica S.ratio V; let v := constantGauge w S.ratio
  have he : 0 ≤ M*temp x := mul_nonneg hm.le (temp_nonneg x)
  obtain ⟨a,ha,he'⟩ := hE id i.1 L (Lattice.gauge w V) _ he hx hu
  obtain ⟨b,hb,hb'⟩ := hE S.ratio.parent i.1 L (Lattice.gauge v U) _ he hx hv
  have hp : ‖(b,a)‖ ≤ A*(M*temp x) := by rw [Prod.norm_def]; exact max_le hb ha
  obtain ⟨hs,H⟩ := h c f S hP hK k i (b,a); let y : PairLogs G f c := (b,a)
  rw [← mul_assoc] at hp
  have hpr := hp.trans hx'
  have hl : ‖Z S (S.prediction U k) V i‖ = ‖zTest S k i y‖ := by
    have hL : v ∘ S.ratio.embed = w := funext (fun i => by unfold v constantGauge; simp only [Function.comp_apply,S.ratio.embed_parent])
    have hJ := (choice_gauge hS U k v).2; rw [hL] at hJ
    rw [← G.norm_adjoint (w i.1), ← z_turn, ← hJ]
    unfold zTest Z
    rw [he' i (by simp),prediction_near_eq hS _ (represent b) k i (hb'.shrink (by rw [separation_self,zero_add,hP]; unfold L LocalJet.allot; omega))]
  change ‖Z S (S.prediction U k) V i‖ ≤ _; rw [hl]
  let l := zLin S b a i
  have he := norm_add_le (zTest S k i y-l) l
  rw [sub_add_cancel] at he
  refine (he.trans (add_le_add (H hpr) hs)).trans ?_
  have hj : C*‖y‖^2 ≤ C*r*‖y‖ := by
    rw [sq, mul_assoc]; exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hpr (norm_nonneg _)) hC.le
  change _ ≤ C*(1+r)*(A*M)*temp x; linarith only [hj, mul_le_mul_of_nonneg_left hp (show 0 ≤ C*(1+r) by positivity)]
end YM.AnalyticBridge.SectorAffine.Offset
