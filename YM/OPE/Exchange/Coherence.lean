import YM.OPE.Exchange.Small
/-!
# Physical projection convention: unit, mixed words, limits and coherence

These results concern the actual filtration spaces and laws, not only the
kinematic spin/equations of a comparison theory. Inputs may be given in any
true filtration level. At each fixed degree the sheet reads *unaltered values*
of equations/unit & other fields on its eventual domain. Junk outside handled
by the zero convention for readings. `shadow` expresses an optional packaged
matching vector, here an exact readout on true fields at every finite horizon.
It compares coherently at successive horizons and, via `compatible_shadows`,
works directly with every character phase. Auxiliary data appearing in the
proof of bounds (e.g. `grid_remainder`) are **not** this continuum matching
prescription. Their selection & convergence were local to those proofs.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE
open Function Set Filter Lattice RG Next.Extract Bid OS Ground Spec Prescription Table
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{L:Register G} {A T: Table L} {P0:DiffPlan A}(P:Prescription P0)(hA:A.Hierarchy) (hp:P0.Inclusions A) (hP:P.Coherent) {I J:Type} [Fintype I][Fintype J] (v:I→L.Token)(i:Mode P0){x:I→E4}{y:J→E4}{d f:ℕ} {o:E4}

/-- Matching vector in the actual graded spaces. Not some limit taken
along an exterior-dependent extraction. -/
def shadow (P:Prescription P0)(d:ℕ)(x:I→ E4)(p:I→L.Token)(o:E4): A.Field d :=∑ i∈ bands P0 d,P.ope i x p o • P.loaded i d

lemma shadow_projection (ha : i∈ bands P0 d) : P.Coherent → P.test i d (shadow P d x v o) = P.ope i x v o:=by
    intro h; rw [shadow,map_sum]; simp_rw [map_smul]; rw [Finset.sum_eq_single_of_mem _ ha,(h d).bothWays i i ha ha,if_pos rfl]; simp
    intro j hj hij; rw [(h d).bothWays i j ha hj,if_neg hij.symm,smul_zero] -- argument orientation
lemma compatible_shadows (hx: T.Hierarchy)(hh:T.respects A)(h : P0.Inclusions T)(w:J→ L.Token)(hy:Injective (beside (sole o) y)) : observeOne A T o y w d (shadow P d x v o)= P.truncated T d x v o y w:=by
    unfold shadow truncated termRead; simp only [map_sum]; refine Finset.sum_congr rfl fun i hi=> ?_; rw [map_smul,P.evaluateProjection T w h hx.laws.toSymmetric hh hy i hi]; rfl -- not need Coherent actually
include hA hp hP
lemma above_shadow (h:d≤ f) : ∑ i∈ bands P0 d,P.test i f (shadow P f x v o) • P.loaded i f=P0.rise h (shadow P d x v o):=by
    conv_rhs=> rw [shadow,map_sum]
    refine Finset.sum_congr rfl fun i hi=>?_ ; rw [map_smul,P.load_next hA.laws.toSymmetric hp i hi h,shadow_projection P v i ((full_bands ..).mpr (((full_bands ..).mp hi).trans h)) hP]

omit hA hp hP in
/-- Estimate the difference of a finite auxiliary physical match to the
coefficient in grade d using only its errors at the fixed detectors, not
using exteriors later added to the calculation. (For the actual Wilson
auxiliary matches the needed transfers are proved directly by `det_cost`,
`forest`-independent and valid without this abstraction.) -/
lemma near_shadow {A':A.Field d} {κ:Exterior L→ℝ}
    (h:∀ x'∈ (P.sheet i).support, ‖reading A x v o x'- A.spectra d A' x'‖ ≤ κ x') : ‖P.ope i x v o - P.test i d A'‖ ≤ ∑ u∈ (P.sheet i).support, ‖(P.sheet i) u‖*κ u :=by
    unfold ope test; rw [computes, ← Finset.sum_sub_distrib]; simp_rw [← mul_sub]
    exact (norm_sum_le ..).trans (Finset.sum_le_sum (fun i' hi=> by simpa [norm_mul] using mul_le_mul_of_nonneg_left (h i' hi) (norm_nonneg ((P.sheet i) i')))) -- simpa direction

lemma valid_on_pins (i':I){z u:L.Token} (h:A.pin _ (A.project _ z.snd)= A.pin _ (A.project _ u.snd)):
    P.ope i x (update v i' z) o=P.ope i x (update v i' u) o:=by
    cases le_total z.fst u.fst with
    | inl hz=> symm; exact respectsLabel P v hP hA.laws.toSymmetric hp i' hz (A.pin_inj _ ((P0.stays hA.laws.toSymmetric hp ..).trans h)) i
    | inr hz=> exact respectsLabel P v hP hA.laws.toSymmetric hp i' hz (A.pin_inj _ ((P0.stays hA.laws.toSymmetric hp ..).trans h.symm)) i -- .. in projection field
omit hP hp
lemma null_words (i': I) (hi:(v i').2∈ A.null (v i').1) : P.ope i x v o = 0:=by
    have hz(p:Exterior L) : reading A x v o p=0:=by
       unfold reading; try dsimp only; split; swap; rfl
       next hx=>
       let Y:= beside (fun i=>x i-o) (bearing p); let B:=beside v p.letter; unfold observe worded; rw [A.readAt]; let a: I⊕Fin p.n:= .inl i'; obtain ⟨i,h⟩:= (runNames (I⊕Fin p.n)).surjective a; exact A.each_place hA.laws.toSymmetric hi (runs_conf.mpr hx) (B ∘ runNames _) i (by change B (runNames (I⊕Fin p.n) i)=_; rw [h]; rfl)
    unfold ope; simp_rw [hz,mul_zero]; exact Finset.sum_const_zero

/-- Adjoining a unit is allowed (reading's collars are still for all inputs).
`Prop` about agreement below outside collisions. -/
lemma unit_words {t:E4}(d:ℕ)(h:∀ u∈ (P.sheet i).support, Injective (beside (away (beside (sole t) x) o) (bearing u))) : P.ope i (beside (sole t) x) (beside (sole (L.one d)) v) o= P.ope i x v o :=by
    have he(u:Exterior L) (hu:u∈ (P.sheet i).support): reading A (beside (sole t) x) (beside (sole (L.one d)) v) o u= reading A x v o u:=by
       let B:= bearing u; let A1:= beside (sole (t-o)) (beside (away x o) B); let A2:= beside (away (beside (sole t) x) o) B; let z:= Equiv.sumAssoc Unit I (Fin u.n); have hV: A1 ∘ z=A2:= funext fun i=> by rcases i with (i|i)|i<;>rfl
       have h2: Injective A2:= h u hu; have h1: Injective A1:=by rw [← hV] at h2; intro i j hij; obtain ⟨i,rfl⟩:= z.surjective i; obtain ⟨j,rfl⟩:= z.surjective j; exact congr_arg z (h2 (show (A1 ∘ z) i = _ from hij))
       let v0:= sole (L.one d); let v1:= beside v0 (beside v u.letter); have hH : beside (beside v0 v) u.letter=v1 ∘ z:= funext fun i=> by rcases i with (i|i)|i<;> rfl
       unfold reading; change (if Injective A2 then observe A A2 (beside (beside v0 v) u.letter) else 0) =(if Injective (beside (away x o) B) then observe A (beside (away x o) B) (beside v u.letter) else 0); rw [if_pos h2,if_pos (beside_distinct.mp h1).2.1,← local_one_mem A (p:=t-o) d _ _ hA.laws h1]; change observe A A2 _ = observe A A1 _; rw [hH,← hV]; exact perm_observe A hA.laws.toSymmetric z v1 h1
    unfold ope; exact Finset.sum_congr rfl fun u hu=>congr_arg _ (he u hu)

private def inputPoints (I:Type)[Fintype I] : (I→E4)→L[ℝ] Points (Fintype.card I):=
   { toFun:= fun x=> points (x ∘ runNames I), map_add':= fun _ _=> by ext; rfl, map_smul':=fun _ _=> by ext; rfl, cont:= by unfold points; fun_prop }
lemma smooth_ope (h:∀ u∈ (P.sheet i).support, Injective (beside (away x o) (bearing u))) : ContDiffAt ℝ ∞ (fun p:(I→E4)×E4=> P.ope i p.1 v p.2) (x,o):=by
    apply ContDiffAt.sum (s:=(P.sheet i).support) (f:=fun u (g:(I→E4)×E4)=> (P.sheet i) u * reading A g.1 v g.2 u) ?_
    intro u hu; apply contDiffAt_const.mul (𝕜:=ℝ); let X: ((I→E4)× E4)→ I⊕Fin u.n → E4:=fun g => beside (away g.1 g.2) (bearing u); let Θ (b) := observe A b (beside v u.letter); have he: ContDiff ℝ ∞ X:= by apply contDiff_pi.mpr; intro i; rcases i with i|i; show ContDiff _ _ (fun p:(I→E4)×E4=> p.1 i - p.2); fun_prop; exact contDiff_const
    have hv: ContDiffAt ℝ ∞ Θ (X (x,o)):=by
       unfold Θ observe worded; simp only [A.readAt]; have hg:inputPoints _ (X (x,o))∈ conf _:= runs_conf.mpr (h u hu); exact ContDiffAt.comp (f:=inputPoints _) (X (x,o)) ((A.smooth_read hA.smooth _) _ hg|>.contDiffAt ((conf_open _).mem_nhds hg)) (inputPoints (I⊕Fin u.n)).contDiff.contDiffAt
    refine (ContDiffAt.congr_of_eventuallyEq (hv.comp _ he.contDiffAt) (((he.continuous.continuousAt (x:=(x,o))).tendsto.eventually (p:=fun a=> Injective a) (open_inj.mem_nhds (h u hu))).mono (fun i hi=> ?_)))
    unfold reading; exact if_pos hi
end YM.OPE
