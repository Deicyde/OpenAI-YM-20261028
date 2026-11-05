import YM.Contacts.Normal.AxisTaylor

/-! # Taylor estimates in compact shells

Return from the scalar-axis Taylor argument. Bounds include **all derivatives in the ambient space** through requested finite test order. Implement the rescaling lemma for composition within an ambient dilation as used with every separating partition.
-/
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.Contacts.Normal
open Function Set Metric MeasureTheory Submodule MultipleContact Panel
open scoped Topology BigOperators Classical ContDiff InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E][InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable (K : Submodule ℝ E) {T : Set E} {r U : ℝ} {f : SmoothTests E} {A : E≃L[ℝ] E} {s q : ℝ}

def scaledField (f : SmoothTests E) (p : E × ℝ) : ℂ:= f.val (slide K p.2 p.1)
lemma onScale (f : SmoothTests E) : ContDiff ℝ ∞ (scaledField K f) := (infSmooth f).comp (slide_smooth K)
lemma atoms_equal (f : SmoothTests E) (n : ℕ) (a : ℝ) (x : E) : (vertical E).atom n (scaledField K f) (x,a)=(piece K n f).val (slide K a x) := by
   let p:E:= K.starProjection x; let q : ℝ →L[ℝ] E:= ContinuousLinearMap.toSpanSingleton ℝ p; let φ(y:E):=f.val (y+(x-p))
   have hs : ContDiff ℝ ∞ φ:= (infSmooth f).comp (contDiff_id.add contDiff_const)
   have he : ∀a, scaledField K f (x,a)=φ (q a) := fun a=> by unfold scaledField; rw [slide_formula,add_comm]; rfl
   rw [vat _ (onScale ..),piece_formula, slip_away, slip, funext he]; unfold coeff
   change (↑n.factorial:ℝ)⁻¹ • iteratedFDeriv ℝ n (φ ∘ q) _ _=_
   rw [q.iteratedFDeriv_comp_right hs _ (le_inf_order n)]; change _ • iteratedFDeriv ℝ n φ (q 0) _=_; rw [map_zero]; unfold φ; rw [iteratedFDeriv_comp_add_right,zero_add]; rfl
lemma whole_equal (f : SmoothTests E) (n : ℕ)(a : ℝ)(x : E) : (vertical E).atoms n (scaledField K f) (x,a)=(jet K n f).val (slide K a x) := by rw [jet_formula]; exact Finset.sum_congr rfl fun i _=> atoms_equal K f i a x

/-- On a compact x-set. No assumptions on support of f. -/
structure BillOn (n m : ℕ) (U : ℝ) (c : ℝ) (T : Set E) : Prop where
   active {f : SmoothTests E}{A : ℝ} : Jet (n+m+1) univ f.val A → ∀ a∈Icc 0 U,
        Jet n T (f.val ∘ slide K a) (c*A)
   remainds {f : SmoothTests E}{A : ℝ} : Jet (n+m+1) univ f.val A → ∀ a ∈ Icc 0 U,
        Jet n T ((f-jet K m f).val ∘ slide K a) (c*A*a^(m+1))
   parts {f : SmoothTests E}{A : ℝ} : Jet (n+m+1) univ f.val A → ∀ a > (0:ℝ), ∀ i, i ≤ m → Jet n T ((piece K i f).val ∘ slide K a) (c*A*a^i)
lemma from_compact (T : Set E)(hT : IsCompact T)(U : ℝ)(hU : 0 ≤ U)(m n : ℕ) : ∃ c ≥ (1:ℝ), BillOn K n m U c T:= by
   let N:=n+m+1
   obtain ⟨B,hB,hP⟩:= controls (slide_smooth K) (hT.prod (isCompact_Icc (a:=0) (b:=U))) N
   let c := (N.factorial:ℝ)*B^N
   have h : ∀ (f : SmoothTests E) (A : ℝ), Jet N univ f.val A → Jet N (T ×ˢ Icc 0 U) (scaledField K f) (c*A) := by
      intro f A h; apply (hP.compose h hB (slide_smooth K) (infSmooth f)).mono; apply le_of_eq; unfold c; ring
   refine ⟨c, one_le_mul_of_one_le_of_one_le (by exact_mod_cast Nat.factorial_pos N) (one_le_pow₀ hB), fun {f A} hp a ha=>?_,fun {f A} hp a ha=> ?_, fun {f A} hp a ha i hi=>?_⟩
   · exact (slice_bill (onScale ..) _ a (h f A hp) ha).weaker (show n ≤ N by omega)
   · refine (axis_remainder (onScale K f) (Icc 0 U) (h f A hp) m n (by omega) a ha.1 (Icc_subset_Icc le_rfl ha.2)).near fun x hx=>?_ ; filter_upwards with y; change f.val _ - _ = f.val _-_; rw [whole_equal] -- not mem support
   apply (axis_piece_budget (onScale K f) _ (h f A hp) i n (by omega) (left_mem_Icc.mpr hU) a).enlarge (by rw [abs_of_pos ha]) (by rfl) le_rfl |>.near; exact fun x hx=> Filter.Eventually.of_forall fun y=> atoms_equal K f i a y

lemma whole_bill (m n) (U : ℝ){T : Set E} {c : ℝ} (h : BillOn K n m U c T) (hc : 0 ≤ c) {a : ℝ} (ha : 0 < a) {u:ℝ} (hf : Jet (n+m+1) univ f.val u) : Jet n T ((jet K m f).val ∘ slide K a) ((m+1:ℝ)* (c*u)*(max 1 a)^m) := by
   have hw:=hf.pos; have hs:= (Jet.join (Finset.range (m+1)) (p:=fun i=>(piece K i f).val ∘ slide K a) (fun i hi=> h.parts hf a ha _ (Nat.le_of_lt_succ (Finset.mem_range.mp hi))) (fun i=> (infSmooth _).comp (slide K a).contDiff))
   apply (hs.mono ?_).near
   · intro x hx; filter_upwards with y; change _=(jet _ _ f).val _; rw [jet_formula]; rfl
   have hp(i:ℕ)(hi:i≤ m) : a^i ≤ (max 1 a)^m:= (pow_le_pow_left₀ ha.le (le_max_right ..) _).trans (pow_le_pow_right₀ (le_max_left ..) hi); refine (Finset.sum_le_sum (fun i hi=> mul_le_mul_of_nonneg_left (hp i (Nat.le_of_lt_succ (Finset.mem_range.mp hi))) (mul_nonneg hc hw))).trans ?_; simp; ring_nf; rfl -- maybe extra
-- normalized tests transform to anisotropic A' = A∘Slide(t)
def composed (A : E≃L[ℝ] E)(f : SmoothTests E) : SmoothTests E:= ⟨f.val ∘ A.toContinuousLinearMap,(infSmooth f).comp A.toContinuousLinearMap.contDiff⟩
lemma amount_aniso (f : SmoothTests E)(A : E≃L[ℝ] E) {r : ℝ}(h : Proper A r K) (x:E)(i : ℕ) : (piece K i f).val (A x) = (piece K i (composed A f)).val x:= by
   simp_rw [piece_formula]; rw [show (composed A f).val=f.val ∘ A.toContinuousLinearMap from rfl,A.toContinuousLinearMap.iteratedFDeriv_comp_right (infSmooth f) _ (le_inf_order i)];
   change _ • iteratedFDeriv ℝ i f.val _ (fun _=>K.starProjection (A x)) = _ • iteratedFDeriv ℝ i f.val (A (x-K.starProjection x)) (fun _=> A (K.starProjection x))
   rw [h.before,h.normal,h.acts _ (K.starProjection_apply_mem x)]
lemma whole_aniso (f : SmoothTests E)(A : E≃L[ℝ] E) {r : ℝ}(h : Proper A r K) (x:E)(i : ℕ) : (jet K i f).val (A x)=(jet K i (composed A f)).val x:= by rw [jet_formula,jet_formula]; exact Finset.sum_congr rfl fun i _=> amount_aniso K f A h x i

lemma scale_window (s : ℝ)(A : E≃L[ℝ] E){r : ℝ}(h : Proper A r K) (x:E) : (window K s).val (A x)= (window K 1).val ((r/s) • x) := by
   change (↑(cutoff s _) : ℂ)= (↑(cutoff 1 _):ℂ); unfold cutoff; congr 2
   rw [h.normal x, map_smul,norm_smul,norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
   simp only [mul_pow,sq_abs,one_pow,div_one,div_pow]; ring
-- alternative normalization in term
lemma cash_a (s : ℝ)(A : E≃L[ℝ] E) {r a : ℝ}(h : Proper A r K) (ha:a≠0)(f : SmoothTests E)(m:ℕ) : (composed ((resize K a ha).trans A) (deviation K s m f)).val = ((composed A f).val ∘ slide K a) - (fun x=> (window K 1).val ((r*a/s) • x)) * ((jet K m (composed A f)).val ∘ slide K a) := by
  funext x; have hW : (window K s).val (A (slide K a x))= _ := scale_window K s _ (h.grant a ha) x
  change f.val (A (slide K a x)) - ((window K s).val (A (slide K a x)))*(jet K m f).val (A (slide K a x))= _
  rw [hW,whole_aniso K f A h]; rfl
end YM.Contacts.Normal
