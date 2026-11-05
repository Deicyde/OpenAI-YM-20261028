import YM.Pert.Parity.Series
/-! Bare local-source parity, transported to the *same* Maxwell quotient, not a claim that interacting source kernels are even at positive spacing. -/
set_option autoImplicit false
set_option maxHeartbeats 220000
noncomputable section
namespace YM.Pert.Parity
open MeasureTheory Lattice Orb Function Labels RawLabels Extra.FD Full Maxwell
open scoped Topology Matrix.Norms.Frobenius
variable {G : Gauge} {n : Side}
local notation "coef" => PowerSeries.coeff (R:=ℂ)
/-- Slot sign also on nonpure operators. -/
def shadow (G : Gauge) := changed (G:=G) (fun _ => -LinearMap.id)
@[simp] lemma shadow_read (A : Jet G) (p : Pol G) : read A (shadow G p) = read (-A) p := by rw [shadow,eval_changed]; rfl
lemma shadow_X (z : Key G) : shadow G (MvPolynomial.X z) = - MvPolynomial.X z := by
  apply eval_ext
  intro A; rw [shadow_read,map_neg]; simp [Labels.read, Labels.coord]
lemma shadow_C (c : ℂ) : shadow G (MvPolynomial.C c) = MvPolynomial.C c := by simp [shadow,changed]
lemma shadow_tame_pair (h : ℝ) (o : Site n) (x : Coords G n) {d : ℕ} (v : Aux G d) (p : Pol G) : pairEval h o (-x) (-v) (shadow G p) = bounce (pairEval h o x v p) := by
  have hink : ∀ z, ink (-v) z = -ink v z := by intro z; unfold ink; split <;> simp_all only [Pi.neg_apply,Complex.ofReal_neg,mul_neg,Complex.ofReal_zero,mul_zero,neg_zero]
  induction p using MvPolynomial.induction_on with
  | C c => unfold pairEval; rw [shadow_C, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_C, ps_const]
  | add p q hp hq => simp only [map_add]; unfold pairEval at *; rw [map_add,map_add,hp,hq,map_add]
  | mul_X p z hp => unfold pairEval at *; rw [map_mul,map_mul,map_mul,shadow_X,map_neg,MvPolynomial.eval₂Hom_X',map_mul,hp,MvPolynomial.eval₂Hom_X',map_add,ps_const,hink,map_neg,neg_add_rev, bare_neg,map_neg]; abel
lemma avg_reflect {d : ℕ} (h : ℝ) {p q : JetArray (Aux G d)} (hp : Ready p) (hr : ∀ u, p (-u) = bounce (q u)) : avg h p = bounce (avg h q) := by
  ext1 m
  simp only [PowerSeries.coeff_rescale,avg,auxLaw,PowerSeries.coeff_mk, ←integral_cloud _ (fun v => coef m (p v)) ((bareTame_integrable h (hp m)).aestronglyMeasurable), hr, integral_const_mul]
lemma column_reflect (d) (h : ℝ) (o : Site n) (p : Pol G) (v) : Full.column d h o (shadow G p) (-v) = bounce (Full.column d h o p v) := by
  rw [auxiliary, auxiliary]; exact avg_reflect h (leg_ready h o (-v) (shadow G p)) (fun _ => shadow_tame_pair ..)
lemma product_reflect {I : Type} [DecidableEq I] (s : Finset I) (e : I→ℕ) (h : ℝ) (o : I→Site n) (p : I→Pol G) (v) : product e h s o (shadow G ∘ p) (-v) = bounce (product e h s o p v) := by simp [product, Finset.prod_apply,column_reflect]
lemma amplitude_reflect {I : Type} [DecidableEq I] (s : Finset I) (e : I→ℕ) (h : ℝ) (o : I→Site n) (p : I→Pol G) : amplitude e h s o (shadow G ∘p)= bounce (amplitude e h s o p) := normalize_reflect (Full.product_ready _ _ _ _ _) (fun _=>product_reflect ..)

lemma shadow_commute (G : Gauge) (e : (i : ℕ) → Module.End ℝ (Taylor G i)) (q : Pol G) : changed e (shadow G q) = shadow G (changed e q) := by
  apply eval_ext
  intro A
  simp only [shadow_read, eval_changed]; apply congrArg (fun A => Labels.read A _)
  funext i
  change -(e i (A i))=e i (-(A i)); rw [map_neg]

lemma shadow_conj (q : Pol G) : shadow G (Labels.conjPol q) = Labels.conjPol (shadow G q) := by apply eval_ext; intro A; rw [shadow_read,Labels.conj_value,Labels.conj_value,shadow_read]
lemma shadow_colored (u : G.El) (q : Jet G) : -(colored u q)=colored u (-q) := by funext j; unfold colored; rw [Pi.neg_apply, Pi.neg_apply,map_neg]
variable {d : ℕ}
def wash (G : Gauge) (d : ℕ) : Labels.Label G d →ₗ[ℂ] Label G d where
  toFun p := ⟨shadow G p.val,moved_limit p.property.1 _,fun A u=> by rw [shadow_read, shadow_read]; change read (-(colored u A)) _= _; rw [shadow_colored]; exact p.property.2 ..⟩
  map_add' a b := Subtype.ext (map_add (shadow G) a.val b.val)
  map_smul' r a := Subtype.ext (map_smul (shadow G) r a.val)
@[simp] lemma wash_unit : wash G d (Labels.unit G d) = Labels.unit G d := Subtype.ext (map_one (shadow G))
lemma wash_involution (p) : wash G d (wash G d p) = p := Subtype.ext (eval_ext _ _ fun A=> by change read A (shadow G (shadow G p.val))=read A p.val; rw [shadow_read, shadow_read,neg_neg])
lemma wash_fixed (q : Label G d) : fixedPolynomial G d (wash G d q) = wash G d (fixedPolynomial G d q) := Subtype.ext (shadow_commute G _ q.val)
lemma wash_turn (q : Label G d) (s : Ortho) : shadow G (Labels.tensor s q).val = (Labels.tensor s (wash G d q)).val := (shadow_commute ..).symm

def Coat (F : Frames G) (d) := enroll F d ∘ₗ wash G d ∘ₗ physicalLabel F d
variable (F : Frames G) (p : Full.Source (Frame:=F) d)
lemma Coat_def : Coat F d p = enroll F d (wash G d (physicalLabel F d p)) := rfl
lemma Coat_lifts : physicalLabel F d (Coat F d p)=wash G d (physicalLabel F d p) := by
  have hf : fixedPolynomial G d (physicalLabel F d p)=physicalLabel F d p := by rw [←embed_round F (physicalLabel F d p),physical_round]
  rw [Coat_def,embed_round,wash_fixed,hf]
lemma Coat_round : Coat F d (Coat F d p)=p := by conv_lhs=> rw [Coat_def]; rw [Coat_lifts,wash_involution,physical_round]
lemma Coat_unit : Coat F d ((freeTable F).unit d)=(freeTable F).unit d := by rw [Coat_def,physical_unit,wash_unit];exact UVNext.FreeStress.pin_unit ..
lemma Coat_spin (s : Ortho) : rideO F s d (Coat F d p) = Coat F d (rideO F s d p) := by
  have he : Function.Injective (physicalLabel F d) := fun a b h=>(physical_round F a).symm.trans ((congrArg (enroll F d) h).trans (physical_round F b))
  apply he
  rw [physical_ortho,Coat_lifts, Coat_lifts,physical_ortho]; exact Subtype.ext ((shadow_commute ..))
lemma Coat_inherit (q : Label G d) : Coat F d (enroll F d q) = enroll F d (wash G d q) := by simp only [Coat_def, embed_round,← wash_fixed, enroll_fixed]
lemma Coat_conj : (freeTable F).conj (table_spin F) d (Coat F d p)= Coat F d ((freeTable F).conj (table_spin F) d p) := by
  have he : Injective (physicalLabel F d) := fun a b h=>(physical_round F a).symm.trans ((congrArg (enroll F d) h).trans (physical_round F b)); apply he
  rw [physical_real,Coat_lifts,Coat_lifts,physical_real]; exact Subtype.ext ((shadow_conj ..).symm)

lemma row_reflect (h : ℝ) {r : ℕ} (o : Fin r → Site n) (w : Fin r → Full.Source (Frame:=F) d) : Full.row d F h o (Coat F d ∘ w) = bounce (Full.row d F h o w) := by
  have he : sections d F ∘(Coat F d ∘w)= shadow G ∘(sections d F ∘ w) := funext fun j => congrArg Subtype.val (Coat_lifts F (w j))
  rw [row_def,row_def, he, amplitude_reflect]
lemma profile_reflect (L : Side) {m r : ℕ} (f : Points r→ℂ) (w : Fin r → Full.Source (Frame:=F) d) : Full.profile d r F L m f (Coat F d ∘ w) = bounce (Full.profile d r F L m f w) := by simp only [profile, MultilinearMap.sum_apply, MultilinearMap.smul_apply, row_reflect,map_sum,PowerSeries.smul_eq_C_mul,map_mul,ps_const]

end YM.Pert.Parity
