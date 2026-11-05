import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.FieldCount

/-!
# Real Gram floor -- local part

Chord-patch comparison need not show a globally pure gauge. Work.F01
stencil at each link. Keep budget constant *post-L*. Perturbation on the
cubes pays a β-small factor even after overlapping all links. Normalized
roots must also pay A inverse rates.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Coat
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {P : Teller G} {c f : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio}
variable (X : Coat T F)

def manifest := X.seeds.flags=RG.flags (Pressure.temp X.x) X.V

def current (o : Site c) (u : Directions G f) :=
    Real.sqrt (∑ i∈withinH (atEdge S) o (3*X.B), ‖X.lens u i‖^2)

def response (o : Site c) (u : Directions G f) :=
    Real.sqrt (∑ i∈withinH (root S) o (Pressure.macroR S.patch+2), ‖X.motion u i‖^2)
lemma current_part (o : Site c) (u : Directions G f) (i : Bond f) (he : separation o (atEdge S i) ≤ 3*X.B) :
    ‖X.lens u i‖ ≤ X.current o u := by
  apply le_of_sq_le_sq _ (by unfold current; positivity); rw [current,Real.sq_sqrt (by positivity)]
  exact single_le_sum  (f:=fun i => ‖X.lens u i‖^2) (fun j _ => sq_nonneg _) ((joins ..).mpr he)
lemma response_part (o : Site c) (u : Directions G f) (i : Mention c f) (he : separation o (root S i) ≤ Pressure.macroR S.patch+2) :
    ‖X.motion u i‖ ≤ X.response o u := by
  apply le_of_sq_le_sq _ (by unfold response; positivity); rw [response,Real.sq_sqrt (by positivity)]
  exact single_le_sum (f:=fun i => ‖X.motion u i‖^2) (fun j _ => sq_nonneg _) ((joins ..).mpr he)

/-- Local Poincaré uses hot shell V only via its flags; not assuming input
curvature bounds nor genuine Replica for all U. -/
lemma replies {h C : ℝ} (hR : Room P S T X.x) (hC : 0 < C) (hX : Bounded T P.top.width C)
    (e : Bond f) (he : X.Hot e) (z : Site c → G.El) (hh : 0 ≤ h)
    (hp : ∀ i : Bond c, separation (atEdge S e) i.1 ≤ 2*X.B → G.chord (gauge z X.V i) ≤ h)
    (u : Directions G f) (p : Rod c f) (hk : separation (atEdge S e) (focus S p) ≤ Pressure.macroR S.patch+2) :
    let o := atEdge S e
    ‖barField T X.R (spinRow S z (X.lens u)) p‖ ≤ X.response o u + (C*(2*G.colorScale*((X.B:ℝ)+1)*h))*X.current o u := by
  intro o; let B := X.B
  have hG := hR.frame
  change _ ≤ B at hG
  have hd (i : Site c) (H : separation (focus S p) i≤B+1) : separation o i ≤ 2*B :=
    (separation_triangle _ _ _).trans (show separation (atEdge S e) (focus S p) + separation (focus S p) i ≤ _ by omega)
  have ht i' (H : separation (focus S p) (atEdge S i') ≤ B+1) := X.current_part o u i'
    ((hd _ H).trans (by unfold B; omega))
  have he' := active_far X.seeds _ he
  have hy : X.selected 1 (spot S p) := by
    have hv : X.addr 1 (spot S p)=focus S p := by rw [addr,← cost_is_here]; simp
    rw [selected,hv]; apply clear he'; unfold o B at *; omega
  have hx := X.response_part o u (1,p) (by simpa [o,root] using hk)
  let W := gauge z X.V; let v := spinRow S z (X.lens u)
  have h₁ := spinning hR.accepted hC hX W X.R B 1 p (show 0 ≤ X.current o u by unfold current; positivity) v
    (fun i h => by unfold v spinRow; rw [G.norm_adjoint]; apply ht; simpa [distAt] using h)
    (by unfold B at *; dsimp only [Coat.R,Coat.B,till] at *; omega) hh (fun i h => hp i (hd _ (by simpa using h)))
  rw [turns_here T X.R p 1,flat_strip] at h₁
  obtain ⟨r,H,hP,-⟩ := hR.accepted.feeds
  have hh' : ‖orientedRow T X.R 1 p W v‖ ≤ X.response o u := by
    rw [show W=gauge z X.V from rfl, show v=spinRow S z (X.lens u) from rfl,
      oriented_under T hP, G.norm_adjoint]
    simpa [motion,hy] using hx
  calc
    _ ≤ ‖barField T X.R v p-orientedRow T X.R 1 p W v‖+‖orientedRow T X.R 1 p W v‖ := by
      simpa only [sub_zero] using norm_sub_le_norm_sub_add_norm_sub (barField T X.R v p) (orientedRow T X.R 1 p W v) 0
    _ ≤ _ := by rw [norm_sub_rev]; unfold B at *; linarith

def units (P : Teller G) (K : ℝ) (D : Patch) := K*((box (Pressure.macroR D)).card:ℝ)*
    (Fintype.card PlaqAxes:ℝ)*(Real.sqrt P.top.clip.direct)⁻¹ + (Real.sqrt P.bind.penalty)⁻¹
lemma units_pos (P : Teller G) {K : ℝ} (h : 0 ≤ K) (D : Patch) : 0 < units P K D := by
  have := P.top.clip.quadratic_pos; have := P.bind.penalty_pos; unfold units; positivity

lemma driving (hR : Room P S T X.x) {C K h : ℝ} (hC : 0 < C) (hX : Bounded T P.top.width C)
    (hK : 0 ≤ K) (e : Bond f)
    (hs : ∀ U : Config G f, SliceSet S F U → usable S U (S.ratio.parent e.1) X.k →
      Bid.Cops (S := S) U 1 (S.prediction U X.k) e K)
    (he : X.Hot e) (z : Site c → G.El) (hh : 0 ≤ h)
    (hp : ∀ i : Bond c, separation (atEdge S e) i.1 ≤ 2*X.B → G.chord (gauge z X.V i) ≤ h)
    (u : Directions G f) :
    let o := atEdge S e
    ‖X.lens u e‖ ≤ units P K S.patch * (X.response o u + (C*(2*G.colorScale*((X.B:ℝ)+1)*h))*X.current o u) := by
  intro o
  let W := spinRow S z (X.lens u); let w := toLog W
  let k := Pressure.macroR S.patch
  let A := Real.sqrt P.top.clip.direct; let Q := Real.sqrt P.bind.penalty
  have hA : 0<A := by have := P.top.clip.quadratic_pos; unfold A; positivity
  have hQ : 0<Q := by have := P.bind.penalty_pos; unfold Q; positivity
  let E := X.response o u + (C*(2*G.colorScale*((X.B:ℝ)+1)*h))*X.current o u
  have hx : ∀ i∈F.trunks,collect G w i=0 := by
    intro i hi; unfold w; rw [collects]
    have h' : ¬ X.Hot i := fun hs => hs.1 hi
    simp [W,spinRow,lens,h']
  have hg := Work.F01.link_bound S (funds_branch hR.accepted) F X.k w hx _ hK e hs
  have hr (p : Rod c f) (hl : separation o (focus S p) ≤ k+2) := X.replies hR hC hX _ he z hh hp u p hl
  let pt (i : Cover) := wrap f i + S.ratio.embed o
  have hU (b : Cell f) (h : separation o (S.ratio.parent b.1) ≤ k+2) : ‖faceCurl b w‖ ≤ A⁻¹*E := by
    have hh := hr (.inl (b,false)) h
    change ‖bareCut T.high T.up X.R w (b,false)‖ ≤ E at hh
    unfold bareCut at hh; simp only [hR.accepted.high,Bool.false_eq_true,↓reduceIte] at hh
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hA] at hh
    exact le_of_mul_le_mul_left (hh.trans_eq (by rw [← mul_assoc,mul_inv_cancel₀ hA.ne',one_mul])) hA
  have hM i (hi : i∈box k) (p : PlaqAxes) : ‖faceCurl (pt i,p) w‖ ≤ A⁻¹ * E := by
    apply hU; dsimp only [pt]
    conv_lhs => arg 1; rw [← S.ratio.embed_parent o]
    exact (Work.E04.parent_separation S.ratio _ _).trans (by have hp := Work.E08.separation_box_add (S.ratio.embed o) hi; omega)
  have hF (i) (hi : i∈box k) := sum_le_sum (s:=univ) (fun p _ => hM i hi p)
  let b : Bond c := (o,e.2)
  have hP : ‖Bid.bills S w (pole b)‖ ≤ Q⁻¹*E := by
    have hh := hr (.inr b) (by dsimp only [b,focus]; simp)
    change ‖zLin S w 0 b‖ ≤ E at hh
    simp only [zLin,norm_smul,Real.norm_eq_abs,hR.accepted.knobs,abs_of_nonneg (Real.sqrt_nonneg _),Pi.zero_apply,zero_sub,norm_neg] at hh
    exact le_of_mul_le_mul_left (hh.trans_eq (by rw [← mul_assoc,mul_inv_cancel₀ hQ.ne',one_mul])) hQ
  have hE : ‖collect G w e‖=‖X.lens u e‖ := by unfold w; rw [collects]; exact G.norm_adjoint ..
  rw [← hE]
  exact hg.trans ((add_le_add (mul_le_mul_of_nonneg_left (sum_le_sum hF) hK) hP).trans_eq (by
    simp only [sum_const,nsmul_eq_mul,card_univ]; unfold A Q k E units; ring))
end YM.ConnectedActivityE6.Coat
