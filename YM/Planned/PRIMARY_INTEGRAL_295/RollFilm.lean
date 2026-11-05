import YM.Euclid.Window
import YM.Planned.PRIMARY_INTEGRAL_295.Unload

/-!
# V_a flat reproduction and pre-length prism pricing

`deliver` works for *all* the canonical retained `destination`s for
this smoothing stage, not just particular torus directions.
Physical station estimates are separate; this is the account
before using comparison of actual history responses.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.PrimaryIntegral295.Carrier
open Function Filter Set Lattice Labels Laurent RG Precision Bloch Exterior Work.F08 Next.Free Place ContinuousMultilinearMap
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {j n t : ℕ}
section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
lemma read_poly (b : Prism E n) : charted b ∈ Place.rangeLt (Axis→E) n :=
    Submodule.sum_mem _ fun i _=> Place.exact_le_band i.isLt (Place.simple (b i))

lemma analyze (f : E4→Axis→E) (h : f ∈ Place.rangeLt (Axis→E) n) : ∃ b : Prism E n, (∀ i,Tensor.Sym (b i)) ∧ charted b=f := by
  obtain ⟨x,hx,rfl⟩ := Place.range_decompose h
  choose b hb he using fun i => Place.pure_sym (hx i)
  refine ⟨b,hb,Finset.sum_congr rfl fun i _ => (he _).symm⟩

def pile (b : Prism E n) := ∑ i, ‖b i‖
lemma pile_cost (q : Prism E (n+1)) : pile q=pile (fun i : Fin n => q i.castSucc) + ‖q (Fin.last n)‖ := Fin.sum_univ_castSucc _
lemma pile_pos (q : Prism E n) : 0 ≤ pile q := Finset.sum_nonneg fun i _=>norm_nonneg (q i)
lemma exposure (q : Prism E (n+1)) : charted q = charted (fun i : Fin n => q i.castSucc) + Tensor.diagonal (q (Fin.last n)) := Fin.sum_univ_castSucc _
lemma exposure_add (q r : Prism E n) : charted (q+r) = charted q + charted r := by
  unfold charted; rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun i _=>rfl
omit [NormedSpace ℝ E] in
lemma shell_add (f g : E4 → (Axis → E)) : verdict (f+g) = verdict f+verdict g := rfl

structure Reel {P : Side} (L : Lines P) (q r : Prism E n) (C : ℝ) : Prop where
  sym i : Tensor.Sym (r i)
  sameTop : charted r - unitStep P ^ n • charted q ∈ Place.rangeLt (Axis→E) (n-1)
  rolled : applyLine L (verdict (charted q)) = verdict (charted r)
  pay i : ‖r i‖ ≤ C * pile q * unitStep P ^ (i.val+1)

variable [FiniteDimensional ℝ E]

/-- Covers any zero modes, pure gradient-jet
uses full polynomial read.

All tensor types with our normalizations,
so in particular any finite coefficient-norm conversion can be paid
before L.

Does not spend the later marker or path costs. -/
theorem deliver (k : ℝ) (hk : 0 < k) (hj : 4 ≤ j) (ht : 4 ≤ t) (n : ℕ) (h : n ≤ j) :
    ∃ C : ℝ,1≤C ∧ ∀ (P : Flight j t) (q : Prism E n), ∃ r : Prism E n, Reel (linesOf P k) q r C := by
  classical
  letI : CompleteSpace E := FiniteDimensional.complete ℝ _
  induction n with
  | zero =>
    refine ⟨1,le_refl _,fun P q=>⟨q,?_,?_,?_,?_⟩⟩
    · exact fun i=>Fin.elim0 i
    · simp [charted]
    · funext x i; simp [charted,applyLine,stream,verdict]
    exact fun i=> Fin.elim0 i
  | succ n ih =>
    obtain ⟨D,hD,H⟩ := pure_alloc k hk E n hj ht (by omega)
    obtain ⟨c,hc,hb⟩ := ih (by omega)
    refine ⟨c+D,by linarith,fun P q => ?_⟩
    let A := linesOf P k; let u := unitStep P.L; have hu : 0<u:= unitStep_pos _
    let p : Prism E n := fun i => q i.castSucc
    let l := Fin.last n; let v := q l
    obtain ⟨w,hw⟩ := hb P p
    obtain ⟨t,hs,ht1,hy,hg⟩ := H P v
    let a : Prism E (n+1) := Fin.snoc w 0
    have ha : charted a=charted w := by rw [exposure]; simp [a,charted]; try rfl
    refine ⟨a + t, fun i v f => ?_, ?_, ?_,fun i => ?_⟩
    · have hA j : Tensor.Sym (a j) := by
        refine Fin.lastCases ?_ (fun i=>?_) j
        · simp [a, Tensor.Sym]; intros; rfl
        simp only [a, Fin.snoc_castSucc]; exact hw.sym _
      exact congr_arg₂ (·+·) (hA i v f) (hs i v f)
    · let f := charted (F:=E) (n:=n) (fun i=> t i.castSucc)
      let F := Place.rangeLt (Axis→E) n
      rw [exposure_add,ha,exposure t,hy,exposure q]
      change charted w+(f+u^(n+1) • Tensor.diagonal v)-u^(n+1) • (charted p + Tensor.diagonal v)∈F
      simp only [smul_add]
      rw [show charted w+ (f+u^(n+1) • Tensor.diagonal v) - (u^(n+1) • charted p + u^(n+1) • Tensor.diagonal v) =
        charted w + f - u^(n+1) • charted p by abel]
      exact Submodule.sub_mem _ (Submodule.add_mem _ (read_poly w) (read_poly _)) (Submodule.smul_mem _ _ (read_poly _))
    · rw [exposure_add,ha, exposure q,shell_add]
      obtain ⟨x,hx⟩ := royalties _ _ (read_poly p)
      have hf := Place.simple v
      obtain ⟨y,hY⟩ := royalties _ _ (Place.exact_le_band (show l.val < n+1 from l.isLt) hf)
      rw [addLine (stored P k hk ht) _ _ hx hY, hw.rolled]
      exact congr_arg (verdict (charted w) + ·) hg
    · have h1 : c*pile p + D*‖v‖≤(c + D) * pile q := by
        rw [pile_cost]; have hp : 0≤pile p := pile_pos _
        change c*pile p+D*‖v‖≤(c+D)*(pile p+‖v‖); nlinarith [norm_nonneg v]
      let K := u^(i.val+1); have hK : 0≤K := by positivity
      have he i : ‖a i‖ ≤ c*pile p*u^(i.val+1) := by
        refine Fin.lastCases ?_ (fun i=>?_) i
        · simp only [a,Fin.snoc_last,norm_zero]; positivity [pile_pos p]
        simp only [a,Fin.snoc_castSucc]; exact hw.pay i
      apply (norm_add_le (a i) (t i)).trans ((add_le_add (he i) (ht1 i)).trans ?_)
      change c*pile p*K + D*‖v‖*K≤(c+D)*pile q*K
      rw [← add_mul]; exact mul_le_mul_of_nonneg_right h1 hK

lemma accepts_V (k : ℝ) (hk : 0 < k) (P : Flight j t) (ht : 4≤t) (hn : n ≤ j) (C : E4→Axis→E)
    (h : C∈Place.rangeLt _ n) : ∃ f ∈ Place.rangeLt (Axis→E) n,
    f-unitStep P.L^n • C∈Place.rangeLt _ (n-1) ∧ applyLine (linesOf P k) (verdict C)=verdict f := by
  obtain ⟨i,-,hi⟩ := analyze C h
  obtain ⟨c,-,hh⟩ := deliver (E:=E) k hk P.legal ht n hn
  obtain ⟨o,ha,hb,hc,-⟩ := hh P i
  exact ⟨_,read_poly o,hi ▸ hb, hi ▸ hc⟩
end
end YM.Planned.PrimaryIntegral295.Carrier
