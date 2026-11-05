import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Polar
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Stove

/-!
# Costly compulsory derivative seal (difference of logs)

χ, Θ,X common. No assigned Plot hypothesis for ANY expressions. Includes
pay over all signs, angular enhancement only multiplies finite shapes. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {k : Finset ℕ} {R : Rep G f} {X : Coat T F} {z : Air f G} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {x : E}
variable {a A α β γ d η σ W s b μ r Q p q v : ℝ} {j n : ℕ}
variable {V : E→ Config G c} {w : E → Directions G f}
 
lemma royal_metric (p : Mention c f) (U : Directions G f) : Vine.pot X p.1 p.2 U = (scale^2)⁻¹ *(‖Vine.bar X U p‖^2/2) := by
  have hs:= Coat.scale_pos; unfold Vine.pot Vine.bar; split
  next he=> rw [norm_smul, Real.norm_of_nonneg hs.le]; field_simp
  simp

private lemma tot (X : Coat T F) (p : Spot c f) (s : Signed) (h : 0≤v)
    (hp : ∀ i∈parents p, Brush j v 1 (fun x=> bar (vary X (V x)) (w x) (s,i)) x) :
    let s':= (Coat.scale^2)⁻¹*((v*v)*(1+(1+1))^j)
    Brush j (2*s') 1 (fun x=> Vine.costs (vary X (V x)) (w x) s p) x := by
  intro s'; have he : (parents p).card≤ 2 := by rcases p with i|i|i <;> simp [parents]
  have hh:0≤ (Coat.scale^2)⁻¹ := by positivity
  have hu i (hi:i∈parents p):Brush j s' 1 (fun x=> Vine.pot (vary X (V x)) s i (w x)) x := by
    have he (k):= royal_metric (X:=vary X (V k)) (s,i) (w k)
    dsimp only at he; simp_rw [he]; apply (((semi (squared (hp i hi))).trim).smul ((scale^2)⁻¹)).climb _ le_rfl
    rw [Real.norm_of_nonneg hh]
  apply (Brush.spree _ _ _ zero_le_one hu).climb _ le_rfl
  rw [sum_const,nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right (by exact_mod_cast he) (by unfold s'; positivity)

lemma cabinet (P : Teller G) (L : Side) (D : Patch) (hD : D.Branches P.bind G) (K γ W : ℝ) (χ : Chi) (j : ℕ)
    {v p : ℝ→ℝ} (h : Rate G L (-(1/2)) v) (hw : ∀ᶠ x in atTop,0 ≤ v x) (hp : Rate G L 0 p) : ∃ B, Rate G L 0 B ∧
    ∀ᶠ x in atTop, ∀ (c f:Side) (S:StepData c f) (T: Tube G S), S.patch=D→ Works P L x S T→ ShellAccess S G x W K γ →
      ∀ (F:Forest S.ratio) (X: Coat T F), X.x=x→ X.width=K → X.χ=χ → X.manifest → ∀ (E:Type) [NormedAddCommGroup E]
      [NormedSpace ℝ E] (z : E) (U:E→ Config G c) (u : E→ Directions G f), U z=X.V → Mode U z j (v x) →
      ∀ (i:Spot c f) (s:Signed), (∀ j',distAt S j' (s.act (lead S i)) ≤ X.B → X.Hot j' → Brush j (|p x|) 1 (fun k=> u k j') z) →
      Brush j (B x) 1 (fun k=> Vine.costs (vary X (U k)) (u k) s i) z := by
  obtain ⟨A,hA,hY⟩:= Vine.luster P L D hD K γ W χ j h hw
  obtain ⟨B,hB,H⟩:= bounded_stencils P D hD
  let a:=carat D P L 0 B; let f x:= 1+kernelGrowth (radiusB x) G (v x)
  let F x:= ((Fintype.card G.ColorIndex:ℝ)*(|A x| + a*|p x|))*(1+(f x+f x))^j
  have he {p : ℝ→ℝ} (h : Rate G L 0 p) := h.compare (v:=fun x=>|p x|) (Eventually.of_forall fun i=> (abs_abs _).le)
  have hx:=Rate.const (G:=G) (L:=L) (1:ℝ); have hf := hx.add ((jet_growth G L h).weaken (by norm_num))
  have hF: Rate G L 0 F := by
    simpa only [zero_mul,add_zero] using! ((((he (hA.weaken (by norm_num))).add ((he hp).mul_left a)).mul_left _).mul
      ((hx.add (hf.add hf)).pow j))
  refine ⟨fun x=> 2*((scale^2)⁻¹*((F x*F x)*(1+(1+1))^j)),?_,?_⟩
  · simpa only [add_zero] using! ((((hF.mul hF).mul_right _).mul_left _).mul_left 2)
  filter_upwards [hY,room G P L] with x hZ hR c f' S T hS Hp hP F' X hs hχ hy hM E _ _ z V u hV hq i s hu
  subst x
  have hh := hR _ _ S T Hp; have he : (vary X (V z)).manifest := by rw [hV]; exact hM
  have hT := hZ c f' S T hS Hp hP F' X E V z rfl hχ hy hq he
  have hf:=replicaM X D hS Hp.length_eq hh hq B hB (H c f' S T hS Hp.funds) le_rfl P.top.width_pos
  have ht:1≤ f X.x:= le_add_of_nonneg_right hf.pos
  have hx:0≤ a:=hf.basis
  apply tot X i s (show 0 ≤ F X.x by unfold F; positivity)
  intro p' hk
  exact (foe hh (s,p') (hf.tilt le_rfl (show _≤f X.x from le_add_of_nonneg_left zero_le_one) le_rfl le_rfl)
    (fun j=> (hT ((s,p'),j)).climb le_rfl ht) (abs_nonneg _) (fun j hj hg => (hu j (by rwa [show root S (s,p')=s.act (lead S i) from congr_arg s.act
      ((cost_is_here p').trans (congr_arg (lead S) ((parent_iff p' i).mp hk)))] at hj) hg).climb le_rfl ht)
    (abs_nonneg _)).trim
-- tangent logarithm in pledged Pack, include only read l-volume
lemma centralSum (X : Coat T F) (Y : Stores S) (V : E→Config G c) (u u' : E→ Directions G f)
    (U : Config G f)
    (hi : ∀ s i,i∈posted (turnStore s Y) (200*X.B) → Brush j A 1 (fun h=> rootface (vary X (V h)) (u h) U false s i) x ∧
      Brush j a 1 (fun h=> Vine.costs (vary X (V h)) (u' h) s i) x) (hv : ∀ t, u' t=voltage (vary X (V t))) (hA : 0≤A) (hp : 0≤a):
    let b:=(Y.shares:ℝ)*Animals.ballCost (200*X.B+1)*Census.spots S.patch.L
    Brush j (b*(A+a)) 1 (fun t=> chalky (vary X (V t)) (u t) U Y+crispy (vary X (V t)) Y) x := by
  intro b
  have he s : ((posted (turnStore s Y) (200*X.B)).card:ℝ) ≤ b := by
    unfold b; rw [← same_price s Y]; exact_mod_cast Census.postedBound (turnStore s Y) (200*X.B)
  have hh (v:ℝ) (hv:0≤v) (f : E→Signed→Spot c f→ℝ) (h:∀ s i, i∈posted (turnStore s Y) (200*X.B) → Brush j v 1 (fun x=> f x s i) x) :
      Brush j (b*v) 1 (fun i=> averaged (fun s=>∑ j∈posted (turnStore s Y) (200*X.B), f i s j)) x := by
    let u s x := ∑ i∈posted (turnStore s Y) (200*X.B),f x s i
    have hu s: Brush j (b*v) 1 (u s) x := by
      apply (Brush.spree _ _ (fun _=>v) zero_le_one (h s)).climb _ le_rfl
      rw [sum_const,nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right (he s) hv
    apply ((Brush.spree _ u _ zero_le_one (fun i (_:i∈univ)=> hu i)).smul Raw.orientation).climb _ le_rfl
    rw [Real.norm_of_nonneg Raw.orientation_range.1.le,sum_const,nsmul_eq_mul,card_univ]
    unfold Raw.orientation; rw [inv_mul_cancel_left₀ (by positivity)]
  rw [mul_add]
  refine (hh A hA _ ?_).gathering (hh a hp _ ?_)
  · exact fun s i he=> (hi s i he).1
  intro s i he; refine ((hi s i he).2).shimmy (Eventually.of_forall ?_)
  intro t; dsimp only; rw [hv]
end YM.ConnectedActivityE6.Blaze
