import YM.Next.MAXWELL.Ends
import YM.Next.MAXWELL.Flavor

/-!
# Shapes of low real bilinears

When Simple: a nonzero color, so also can separate mixed tests using
that one color. Real label means real before time reflection, even
when represented as a complex linear combination.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Maxwell.Free
open Set Function Filter Tensor Analysis MeasureTheory
open scoped ContDiff Topology BigOperators ComplexOrder InnerProductSpace
variable {G : Gauge} {j l d : ℕ}

def coreColor (h : G.Simple) : G.ColorIndex := by
  haveI := h.nontrivial_color
  exact ⟨0,(by rw [show G.lieDim=Module.finrank ℝ G.Color from G.colorIso.finrank_eq.symm]
               exact Module.finrank_pos)⟩

lemma volumes {G : Gauge} (x : WickPol G) (c : ℝ) : (c:ℂ) • x=c • x := (RCLike.real_smul_eq_coe_smul (K:=ℂ) c x).symm



lemma bit_add (a b : Flavor j) (i : G.ColorIndex) : bit (a+b) i=bit a i+bit b i := by
  obtain ⟨L,hL⟩ := symbol_linear (G:=G) j; simp_rw [bit,← hL]; rw [map_add,map_add]
lemma bit_scale (a : Flavor j) (i : G.ColorIndex) (t : ℝ) : bit (t • a) i=t • bit a i := by
  obtain ⟨L,hL⟩ := symbol_linear (G:=G) j; simp_rw [bit,← hL]; rw [map_smul,map_smul]

theorem team_add (G : Gauge) (a b : Flavor j) (w : Flavor l) : team G (a+b) w=team G a w+team G b w := by
  simp_rw [team,bit_add,add_mul,Finset.sum_add_distrib]
theorem team_smul (G : Gauge) (t : ℝ) (b : Flavor j) (w : Flavor l) : team G (t • b) w=t • team G b w := by
  simp_rw [team,bit_scale,smul_mul_assoc,Finset.smul_sum]

def duetL (G : Gauge) (j l : ℕ) : Flavor j →ₗ[ℝ] Flavor l →ₗ[ℝ] WickPol G where
  toFun a :=
    { toFun := team G a, map_add' b c := by rw [team_swap,team_add,team_swap _ b,team_swap _ c]
      map_smul' t b := by rw [team_swap,team_smul,team_swap _ b]; rfl }
  map_add' a b := LinearMap.ext fun v => team_add ..
  map_smul' t b := LinearMap.ext fun v => team_smul ..

abbrev Panels (j l : ℕ) := Sheet j →ₗ[ℝ] Flavor l

def monoT (x : Flavor j) (y : Flavor l) : Panels j l := x.smulRight y

def canopy (G : Gauge) (j l : ℕ) : Panels j l →ₗ[ℝ] WickPol G where
  toFun D :=
    let B := Module.finBasis ℝ (Sheet j)
    ∑ i, duetL G j l (B.coord i) (D (B i))
  map_add' A D := by simp only [LinearMap.add_apply,map_add,Finset.sum_add_distrib]
  map_smul' c D := by simp only [LinearMap.smul_apply,map_smul, Finset.smul_sum]; rfl

lemma shelter (p : Flavor j) (q : Flavor l) : canopy G j l (monoT p q)=team G p q := by
  let B := Module.finBasis ℝ (Sheet j)
  change (∑ i,duetL G j l (B.coord i) (p (B i) • q))=team G p q
  simp only [map_smul]
  have hp : p=∑ i, p (B i) • B.coord i := by
    apply LinearMap.ext; intro x; rw [LinearMap.sum_apply];
    conv_lhs => rw [← B.sum_repr x]
    simp only [map_sum, map_smul]; exact Finset.sum_congr rfl fun i _ => mul_comm ..
  change _ = (duetL G j l).flip q p
  conv_rhs => rw [hp,map_sum]
  exact Finset.sum_congr rfl fun i _ => ((duetL G j l).flip q).map_smul _ _ |>.symm

/-- Single color witnesses to canopy injectivity when testing distinct orders. -/
lemma extract_canopy (c : G.ColorIndex) {D : Panels j l} (h : j≠l) (A : Sheet j) (B : Sheet l) :
    let F : TaylorTower G := update (update (fun _ => 0) j (fill j (unitColor G c) A)) l (fill l (unitColor G c) B)
    probe F (canopy G j l D) = (D A B:ℝ) := by
  classical
  intro F
  have hi (p : Flavor j) (q : Flavor l) : probe F (team G p q)=((p A * q B : ℝ):ℂ) := by
    simp_rw [team,map_sum,map_mul,bit, symbol_test]; rw [Finset.sum_eq_single_of_mem c (Finset.mem_univ _)]
    · dsimp only [F]; rw [update_self,update_of_ne h,update_self,tasted,tasted]; push_cast; rfl
    intro d _ hd; dsimp only [F]
    rw [update_self, update_of_ne h, update_self]
    rw [show flavor j d p (fill j (unitColor G c) A)=0 from ?_, Complex.ofReal_zero,zero_mul]
    change p (faceMap _ _ _)=_; rw [which, unitPaint c d, if_neg hd,zero_smul,map_zero]
  let W := Module.finBasis ℝ (Sheet j)
  change probe F (∑ i, team G (W.coord i) (D (W i)))= _
  rw [map_sum]; simp_rw [hi];
  rw [← Complex.ofReal_sum]
  apply congr_arg ((↑) : ℝ → ℂ)
  conv_rhs => rw [← W.sum_repr A]
  rw [map_sum, LinearMap.sum_apply]; exact Finset.sum_congr rfl (fun i _ => by rw [map_smul]; rfl)

lemma canopy_faithful (c : G.ColorIndex) (h : j ≠ l) : Injective (canopy G j l) := by
  intro p q he
  apply LinearMap.ext; intro x; apply LinearMap.ext; intro y
  apply Complex.ofReal_injective
  rw [← extract_canopy c h x y,he]; exact extract_canopy c h x y

/-- Recover the real span from the complex span. -/
lemma real_scale (p : WickPol G) (c : ℂ) : realForm (c • p)=star c • realForm p := by
  simp [realForm,← MvPolynomial.C_mul']

lemma real_span {X : Set (WickPol G)} (H : ∀ p∈X, realForm p=p) (p : WickPol G)
    (he : p ∈ Submodule.span ℂ X) (hp : realForm p=p) : p ∈ Submodule.span ℝ X := by
  let K := Submodule.span ℝ X
  let A := (1/2:ℝ)
  suffices ht : ∀ q∈Submodule.span ℂ X,∀ c : ℂ,c • q+realForm (c • q) ∈ K by
    have hv := ht p he (A:ℂ)
    rw [real_scale,hp,Complex.star_def,Complex.conj_ofReal,volumes,← add_smul,show A+A=1 by unfold A; norm_num,one_smul] at hv
    exact hv
  intro q h; induction h using Submodule.span_induction with
  | mem u h =>
    intro c; rw [real_scale,H _ h, ← add_smul, show c+star c=((↑(2*c.re):ℂ)) from ?_,volumes]
    exact Submodule.smul_mem _ _ (Submodule.subset_span h)
    apply Complex.ext <;> (simp; first | done | ring)
  | zero => simp [K]
  | add x y _ _ h k =>
    intro c; rw [smul_add,map_add,add_add_add_comm]; exact Submodule.add_mem K (h c) (k c)
  | smul t p _ h => intro c; rw [smul_smul]; exact h _

lemma tent (p : WickPol G) (h : p∈Teams G j l) (hp : realForm p=p) :
    ∃ D : Panels j l, canopy G j l D=p := by
  have he := real_span (X := {x | ∃ (a : Flavor j) (b : Flavor l), x=team G a b}) (by rintro _ ⟨a,b,rfl⟩; exact realTeam ..) p h hp
  refine (Submodule.span_le.mpr (show {x | ∃ (a : Flavor j) (b : Flavor l), x=team G a b} ⊆ ↑(LinearMap.range (canopy G j l)) from ?_)) he
  rintro _ ⟨a,b,rfl⟩; exact ⟨_,shelter a b⟩



lemma team_square_span (a b : Flavor j) : team G a b∈ Submodule.span ℂ
    (Set.range fun p : Flavor j => team G p p) := by
  let V := Submodule.span ℂ (Set.range fun p : Flavor j => team G p p)
  have he (p : Flavor j) : duetL G _ _ p p∈ V := Submodule.subset_span ⟨p,rfl⟩
  change duetL G j j a b∈ V
  rw [show duetL G j j a b= (1/2:ℂ) • (duetL G j j (a+b) (a+b) - duetL G j j a a - duetL G j j b b) from ?_]
  · exact Submodule.smul_mem _ _ (Submodule.sub_mem _ (Submodule.sub_mem _ (he _) (he _)) (he _))
  rw [show (a+b:Flavor j)=a+b from rfl]
  simp only [map_add,LinearMap.add_apply]
  rw [show duetL G j j b a = duetL G j j a b from team_swap ..,
    show duetL G j j a a + _ + _ - _ - _ = duetL G j j a b + duetL G j j a b from ?_]
  · rw [← two_smul ℂ,smul_smul]; norm_num
  abel

lemma team_feed (G : Gauge) (u : E4) (p : Flavor j) :
    rewired (glide G u) (team G p p)=(2:ℝ) • team G p (feed u j p) := by
  unfold team; rw [map_sum,Finset.smul_sum]; refine Finset.sum_congr rfl fun i _ => ?_
  unfold bit
  rw [Derivation.leibniz,rewired_symbol,consecutive]; rw [two_smul]; rfl
end YM.Maxwell.Free
