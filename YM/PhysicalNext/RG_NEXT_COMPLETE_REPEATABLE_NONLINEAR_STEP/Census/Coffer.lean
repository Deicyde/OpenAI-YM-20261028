import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Census.Mettle
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Height.Hip

/-!
# Before Caller Reservation and Scherzo under identical data
 Proofs from Pledge not just h Offering. `Rich` buys at actual Bundle.
 Use Formation on high. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Height
open Function Filter Set Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling
open Extra.Iteration   Time Supply Input Testing
open ConnectedActivityE6.Blaze Blaze.March Captain PriceCompiler  Silica
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {s : Sheet G} {D : Rolls s} {Θ : Protection D} {W : Delays Θ} {Y : Bar W} {I : Wait Y}
    {Z : ChartRatio G} {K : MapPrices} {P : PostCost D}
    {E : ℕ → ℕ → Exchange} {F : ℕ → ℕ → Postage} {f r b : Return.Wages}
    {q : UVNext.CouplingReset.ResetPrices} {η : ℕ → ℝ} {A : Scouts (F:=F)} {hL : ℕ→ℝ}
    {Q : Targets s K} {p : Expenses Q} {c c' : ℝ} (B : Directed G I Z K P) (R : Register D p f hL)
    {N m n : ℕ}

section hire
variable {P : Teller G} {Q : YM.ConnectedActivityE6.Target G P}
def Skill (p : Q.Expense) (L:Side) (W μ c : ℝ) (o : ConnectedActivityE6.Target.Order G W) (x : ℝ) (j n : ℕ) (χ:Chi) :=
    grow G L x ^ 3 ≤ Real.exp (Q.ε*Pressure.Stores.till x) ∧
    ∀ (c' f : Side) (S : StepData c' f) (T : Tube G S), Works P L x S T → Stamp T→ ∀ (R:RG.Rep G f) (H:Cash W x μ L Q o c T R),
      ∃ (C' d v t A b r B q i : ℝ) (k : ℕ), (∃ N: Captain H j C' d v t A b r B q k χ, Heavy N.conduit) ∧ Armada Q L μ p.earn x i B j k ∧
        collars G i x j n * (salary Q L μ B x j k*(1-1/2)⁻¹) ≤ betaF G x L ^ p.wanting
lemma voyageFare (Q : YM.ConnectedActivityE6.Target G P) (L : Side) : ∀ᶠ x in atTop, grow G L x ^ 3 ≤ Real.exp (Q.ε*Pressure.Stores.till x) := by
  have h:= (Rate.power (G:=G) (L:=L) (a:=3/8)).pow 3|>.mul (Rate.cutoff Q.usable (a:=-2))
  filter_upwards [h.below (by norm_num) 1 zero_lt_one] with x hx
  apply le_of_mul_le_mul_right _ (Real.exp_pos (-Q.ε*Pressure.Stores.till x))
  rw [← Real.exp_add, neg_mul,add_neg_cancel,Real.exp_zero]; exact (le_abs_self _).trans (by simpa only [neg_mul,grow] using hx)
lemma sailing (Q : YM.ConnectedActivityE6.Target G P) : ∃ m:ℕ, ∀ L:Side,m≤L.val → ∀ (X:Q.Expense) (W μ c : ℝ) (o:Target.Order G W), 0<W → 0<μ →
    ∀ j n χ, ∀ᶠ x:ℝ in atTop, Skill X L W μ c o x j n χ := by
  obtain ⟨m,hm⟩:= takeover P Q; refine ⟨m,fun L hL X W μ c o hW hμ j n χ=> ?_⟩
  by_cases he : ∃ D : Patch,D.Branches P.bind G ∧ D.L=L ∧ D.J=P.j
  swap; · exact (voyageFare Q L).mono fun x hx=>⟨hx,fun c f S T h=> (he ⟨S.patch,h.funds.kernel,h.length_eq,h.funds.atStep⟩).elim⟩
  obtain ⟨D,hd,hF,hX⟩:=he; obtain ⟨A,a,C,d,v,t,r,B,q,k,hB,hq,H⟩:=hm L hL D hd j χ W hW μ hμ o
  obtain ⟨y,hg,hK⟩:= Armada.ensemble Q L hμ X.earn X.price (by linarith [X.worth,X.first,X.second]) j k hB
  filter_upwards [voyageFare Q L,H,hg n 0 X.wanting X.reach,hK] with x he' h hh hA
  refine ⟨he',fun c f S T hW hx R I=>?_⟩
  simp only [pow_zero,mul_one] at hh
  exact ⟨C,_,_,_,_,_,_,_,_,_,_,h c f S T (hW.patch hF hX) hx R _ I,hA,(le_abs_self _).trans hh⟩
end hire

-- extra floor

def Aptitude (s : Sheet G) (K : MapPrices) {Q : Targets s K} (p : Expenses Q) (u : ℕ→ℕ) :=
  ∀ j i, StepStages j i → ∀ L:Side,u j ≤ L.val →∀ (W μ c:ℝ) (o: Target.Order G W), 0<W → 0<μ → ∀ k n χ,
      ∀ᶠ x:ℝ in atTop, Skill (p j i) L W μ c o x k n χ

theorem beneath (s : Sheet G) (K : MapPrices) {Q} (p : Expenses (s:=s) (K:=K) Q) : ∃ u, Aptitude s K p u := by
  choose m hm using fun i j=> sailing (Q i j)
  exact ⟨fromMax m, fun j i h L hL W μ c o he hV k n χ=>hm _ _ _ ((le_fromMax m h).trans hL) _ W μ c o he hV k n χ⟩

def Tenement (Z : Delays Θ) := ∀ j x,Z.betaEntry j≤x→∀ i,StepStages j i → Skill (p j i) (D.L j) (f j i) (R.μ j i) (R.c j i) (R.o j i) x
    (s.profile i).order (s.profile i).power Chi.canonical

lemma haste {u} (h : Aptitude s K p u) (hu : ∀ j,u j ≤ (D.L j).val) (V : Delays Θ) :
    ∃ X : Delays Θ, DelayLe V X ∧ ∀ Y : Delays Θ, DelayLe X Y → Tenement R Y := by
  obtain ⟨x,-,hx,H⟩:= collect_upper V.betaEntry _ fun j=> eventually_transitions j _ _ (fun i hi=>
    h j i hi (D.L j) (hu j) _ _ (R.c j i) (R.o j i) (R.consumes j i hi).1 (R.consumes j i hi).2.1 _ _ Chi.canonical)
  exact ⟨{V with betaEntry:=x}, ⟨hx,le_rfl,le_rfl,le_rfl⟩,fun _ h j x hx i hi=> H j x ((h.beta _).trans hx) i hi⟩

variable (hm : m<N) (hr : Receiving R A W c') (h : ∀ N m n,m≤N → Bid.Sworn (B.M.H N m) n G)
    (hQ : ∀ j i:ℕ, StepStages j i → (s.profile i).supportExponent+3≤(p j i).earn) (hu : Rich R c W) (hW : Tenement R W)
    {X X' : RG.Rep G (B.a.S.side (m+1) n)}

include hm h hr hu hQ hW

end YM.PhysicalNext.Repeat.Height
