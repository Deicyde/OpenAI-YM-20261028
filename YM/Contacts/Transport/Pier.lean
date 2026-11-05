import YM.Contacts.Transport.Poller
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
/-!
# Integrating on the Jacobi fibers

Here are `volume` measures (Lebesgue induced by the orthogonal inner product only). When consuming
`Charge`/`Dust` specialize to these instances (not e.g. separately chosen unrelated Haar lengths
on tangent spaces). After Fubini the same root operation(s) can be read with the center parameters
and other remnant positions already fixed, evaluated on the actual restricted test. Remains the
pointwise sum of scores inside that fiber, **not** taking limits of point products with centers
integrated away. Works also when the individual inner positions of any block requiring the remaining
normal Jacobian are far beyond its clearance to other-group positions (projected child). Validity
as a prescription already established with support tests in the ambient region. Do not assert
Integrable of a punctured operator on every such slice without its test/Taylor/placement data;
the integral equality consumes when integrable on the chosen ambient tests. Under the hypotheses
where using in open context in earlier files those contain this input. On the slices one may
also invoke the same estimates in relative stages where the patch support qualifies.
-/
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.Contacts.Transport
open Function Filter Set Metric MeasureTheory Submodule Table Spec Normal OPE Harvest Route Solstice Ordered WithLp
open scoped Topology Classical BigOperators ContDiff TensorProduct InnerProductSpace MeasureTheory
variable {E X : Type}[NormedAddCommGroup E][InnerProductSpace ℝ E][FiniteDimensional ℝ E]
variable {k : ℕ}{T : E→ₗᵢ[ℝ] Points k}{f g : Normal.Group k} {o : Points k}
variable {G:Gauge}{C:Family G}{O:Extraction.Order}{S:Table C.book}{Z:Final C O S}{d : Fin k→ℕ}
variable (M : Devices Z.sector.derivatives)(K : Submodule ℝ E) (c : Kᗮ) (z:Cells S d)
local notation "K!" => T.comp K.subtypeₗᵢ -- macro

-- a restriction preserving all coordinates normal to the cluster.

lemma string (h : normalOn T g≤ K)(hh : plane g≤ LinearMap.range T.toLinearMap)(hz: Collapsed g o) : Ribbon (.refl (Fin k)) (T.comp K.subtypeₗᵢ) T (K.subtypeₗᵢ) c.val (T c.val+o) o 1 0 g:= by
   have he: current (.refl _) g=g:= by rw [carries, Finset.map_refl]
   refine ⟨?_,he.symm ▸ hh, ?_, he.symm ▸ hz, ?_⟩
   · intro v hv; obtain ⟨t,ht⟩:= hh hv; have ht: T t=v:=ht; exact ⟨⟨t,h (show t∈ normalOn T g from (on_plane ..).2 (ht.symm ▸ hv))⟩,ht⟩
   · apply (collapsed_orthogonal g _).2; exact (plane g)ᗮ.add_mem ( (collapsed_orthogonal g _).1 ((local_collapse hh c.val).2 ((normalOn T g).starProjection_apply_eq_zero_iff.mpr (orthogonal_le h c.property)))) ((collapsed_orthogonal g _).1 hz)
   intro i hi x; change (T ((K.subtypeₗᵢ) x+c.val)+o) i=_; rw [map_add,add_assoc]; simp -- Ortho motion
lemma plain : Ribbon.Forms M 1 false (.refl _) g z z := fun i _=> by
    change (⟨_,z i⟩: S.Tag)=(⟨_,M.rotation.act _ 1 (z i)⟩: S.Tag); rw [M.laws.fixes]
lemma plain_press (f : Expression Z.sector.derivatives) : Ribbon.press M 1 0 false f=f:= by
    change shiftExpr 0 (turnExpr M.basis M.rotation 1 f)=_; rw [turn_one M.basis M.rotation M.laws M.hierarchy.laws.toSymmetric M.incl M.coherent,shift_zero]
private lemma ready (Q : Pieces g)(hQ : ∀ j∈Q.parts, normalOn T j≤ K)(hm : ∀ j∈Q.parts,plane j≤ LinearMap.range T.toLinearMap)(ho' : ∀ j∈Q.parts,Collapsed j o) (s:ℝ): Recall false (fun (x:K)=> x.val+c.val) (Ribbon.press M 1 0 false) (parcel ((waySystem (T.comp K.subtypeₗᵢ) M (T c.val+o) d z).full (T.comp K.subtypeₗᵢ) s) Q) (parcel ((waySystem T M o d z).full T s) Q):= by
   let P' := T.comp K.subtypeₗᵢ
   let X:= waySystem P' M (T c.val+o) d z; let Y:= waySystem T M o d z; let p : Normal.Group k↪ Normal.Group k:= current (.refl _)
   have hp(i): p i=i:=by unfold p; rw [carries,Finset.map_refl]
   have ht:Q.parts.map p=Q.parts:=by rw [show p= (.refl _) from Embedding.ext fun i=> hp i,Finset.map_refl]
   suffices he: Recall false (fun (x:K)=> x.val+c.val) (Ribbon.press M 1 0 false) (product Q.parts (X.full P' s)) (product (Q.parts.map p) (Y.full T s)) by rw [ht] at he; exact he
   apply Recall.synopsis p Q.parts _ ( (X.can_use P' s).stands Q) (by rw [ht]; exact (Y.can_use T s).stands Q)
   intro i hi; exact ( (string K c (hQ i hi) (hm i hi) (ho' i hi)).full_flow ((string K c (hQ i hi) (hm i hi) (ho' i hi)).branch_joint (plain M z)) s (Q.nonempty_of_mem_parts hi)) -- direction no rewrite
-- transport each piece separately. Doesn’t require P.root all.
lemma on_land (Q : Pieces g)(hQ : ∀ j∈Q.parts, normalOn T j≤ K)(hm : ∀ j∈Q.parts,plane j≤ LinearMap.range T.toLinearMap)(ho' : ∀ j∈Q.parts,Collapsed j o) (s:ℝ)(p:SmoothTests E)(x:K): localImage M T Q o s z p (x.val+c.val)= localImage M (T.comp K.subtypeₗᵢ) Q (T c.val+o) s z (sampling K.subtypeₗᵢ c.val false p) x:= ((ready M K c z Q hQ hm ho' s).fin Ribbon.confers (siblings (U:=K.subtypeₗᵢ) p) x).symm.trans (plain_press M _)

-- simultaneous integral precision using volume instances canonically assigned.
def piercing : WithLp 2 (Kᗮ × (K:Type _)) ≃ₗᵢ[ℝ] E := by
    let e:= (WithLp.linearEquiv 2 ℝ (Kᗮ × (K:Type _))).trans (Kᗮ.prodEquivOfIsCompl K K.isCompl_orthogonal.symm);
    refine { __ := e, norm_map' := ?_}
    intro x; let f:= (WithLp.ofLp x).fst; let g:= (WithLp.ofLp x).snd; change ‖f.val+g.val‖=_
    have hh: ⟪g.val,f.val⟫_ℝ=0:= f.property g.val g.property
    have hy : ‖f.val+g.val‖^2 = ‖x‖^2:= by rw [add_comm f.val, pow_two, norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ hh, WithLp.prod_norm_sq_eq_of_L2]; change _= ‖f.val‖^2+ ‖g.val‖^2; ring
    nlinarith only [hy,norm_nonneg (f.val+g.val), norm_nonneg x]

variable [MeasurableSpace E][BorelSpace E] [NormedAddCommGroup X] [NormedSpace ℝ X]

-- Upright, canonical Jacobi product maps tangent parameter then normal coordinates. Fubini indep.
abbrev shore (K : Submodule ℝ E) := (MeasurableEquiv.toLp 2 (Kᗮ × (K:Type _))).trans (piercing K).toMeasurableEquiv
lemma reached (a: Kᗮ × (K:Type _)) : shore K a=a.snd.val+a.fst.val:= add_comm a.fst.val a.snd.val
lemma enter_bank : MeasurePreserving (shore K):= (LinearIsometryEquiv.measurePreserving (piercing K)).comp (WithLp.volume_preserving_toLp ..) -- argument count?
omit [NormedSpace ℝ X] in
lemma takeover (f : E→ X)(h:Integrable f): ∀ᵐ c : Kᗮ, Integrable (fun x:K=> f (x.val+c.val)):= by
    have he : Integrable (fun x=> f (shore K x)) ((volume : Measure (Kᗮ)).prod (volume:Measure K)):= (enter_bank K).integrable_comp_of_integrable h
    filter_upwards [he.prod_right_ae] with c hc; simp_rw [reached] at hc; exact hc
lemma shore_price (f : E→X)(h: Integrable f) : (∫ x, f x)= ∫ c : Kᗮ, ∫ x:K,f (x.val+c.val):= by
   rw [← (enter_bank K).integral_comp (shore K).measurableEmbedding f]; change (∫ x,f (shore K x) ∂(volume.prod volume))= _; rw [integral_prod (fun x=>f (shore K x)) ((enter_bank K).integrable_comp_of_integrable h)]; simp_rw [reached]
lemma onshore (Q : Pieces g)(hQ : ∀ j∈Q.parts, normalOn T j≤ K)(hm : ∀ j∈Q.parts,plane j≤ LinearMap.range T.toLinearMap)(ho' : ∀ j∈Q.parts,Collapsed j o)(s:ℝ)(p:SmoothTests E)(U : E→ Expression Z.sector.derivatives → X)(h : Integrable (fun x=> U x (localImage M T Q o s z p x))) : (∫ x,U x (localImage M T Q o s z p x))= ∫ c: Kᗮ,∫ x:K,U (x.val+c.val)
      (localImage M (T.comp K.subtypeₗᵢ) Q (T c.val+o) s z (sampling K.subtypeₗᵢ c.val false p) x):= by rw [shore_price K _ h]; simp_rw [on_land M K _ z Q hQ hm ho']
end YM.Contacts.Transport
