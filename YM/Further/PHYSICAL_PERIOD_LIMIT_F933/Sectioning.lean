import YM.Further.PHYSICAL_PERIOD_LIMIT_F933.Trades
import YM.Further.PHYSICAL_PERIOD_LIMIT_F933.WardPre
import YM.Next.ROTATIONS.Budget
import YM.Next.UV_STRESS.Fringe
import YM.Next.WARD_BIN.Pennies
import YM.Push.GRID_APPROXIMATION.AttachGather
import YM.SectorNext.VACUUM_NORMALIZATION.Bulk


/-!
# Getting a Mark Console of chosen alphabet from Local splitting outputs

In LOCAL_SPLITTING alone can't feed our PSREC (.Purchases)
if supplying on it's `PreData` P only (finite F.Coeff basis). Need
 a splitter on all the Duets. We formulate and give a full bridge here,
 could call even where no prior Work.Config.Measure.PricedSource estimator
 speaks about BASED. Do NOT assume actual Local.{Output,Prices}! Test with the exact
 finite physics antecedents (still enormous/unmet, see Symphony discussion)
 for a coherent *read* on the actual cones. No use of a prismatic option
 ignoring footprint, directly at all contributing j. Tsum of prices after
 kernel calls important, junk prescriptions resulting in divergent spends
 are not relevant even to making flow linear. The orientation issue: to
 actually use this at Revealed also need `Earned.spins`
 on the detecting *source* signal. It is a finite algebra requirement in
 addition to the estimates below. Don't appeal to equivariance of an
 independently commissioned Ledger, see Rental.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.PhysicalPeriodLimitF933.Sectioning
open Function Filter Set MeasureTheory Wilson Lattice RG Precision Supply Pressure Bid Labels Source
    Push.Local Extra.Histories WardBin
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff Classical
variable {G : Gauge} {n : Side} {i j d N m p l : ℕ} {F : Labels.Frame G d} {H : Hol G} {X : SectionData F} {B : Rep G n} {W : Worth}

-- At any stencil with common-payment convention. Need all o contained, in choosing even dummy vs extended supports.

def authenticated (r : Rep G n) (o : Site n) (i : Stripe n) (A : Hol G) (v : ℝ) (x : Baton F n) :=
    let y := castAt i x; y.Format o A r ∧ ∃ c, y.remBound o r v c

def known (r : Rep G n) (o : Site n) (i : Stripe n) (hp : ∀ j, o∈i j) (A : Hol G) (v : ℝ) (hv : 0 < v) : Submodule ℂ (Baton F n) where
  carrier := authenticated r o i A v
  zero_mem' := by
    refine ⟨?_,0,?_⟩
    · -- addresses r over any A
      refine ⟨fun j=> (regular0 r.p (i j) o).1,hp,fun _=>rfl,fun _ _=> vanishing0 _ _ _,fun _ U h=> (h rfl).elim,fun _ h=> (h rfl).elim,fun _ _ _=>rfl,fun _ _ _ _ _=>rfl,fun _=>measurable_const⟩
    refine ⟨0,0,le_rfl,le_rfl,(add_zero 0).le,hv,⟨0, budget0 r.p i, fun j=> (regular0 r.p (i j) o).2⟩,⟨0,by rw [mul_zero]; exact budget0 _ _, fun _=> ⟨le_rfl,fun _=> (norm_zero (E:=ℂ)).le⟩⟩⟩
  smul_mem' := by
    rintro c x ⟨hx,d,ht⟩
    change authenticated _ _ _ _ _ _
    simp only [authenticated]
    have hK : castAt i (c • x) = stretch c (castAt i x) := rfl
    rw [hK]; exact ⟨stretch_format c hx, ‖c‖*d,stretch_rem c ht⟩
  add_mem' := by
    rintro x y ⟨hx,k,hk⟩ ⟨hy,q,hq⟩
    let Y := stretch (-1) (castAt i y)
    have hb : Y.Format o A r := stretch_format _ hy
    have hc := stretch_rem (-1:ℂ) hq
    have hf : x+y=x- (-1:ℂ) • y := by rw [neg_one_smul,sub_neg_eq_add]
    rw [hf]
    exact ⟨sub_funded (H:=A) (Q:=Y) (P:=castAt i x) rfl hx hb, k+‖(-1:ℂ)‖*q,sub_rem (H:=A) (Q:=Y) (P:=castAt i x) rfl hx hb hk hc⟩

abbrev Client (U : RG.History G) (n : Side) (B : Rep G n) (i : Stripe n) (h : ∀ j, (0:Site n) ∈ i j) (z : ℕ) (A : Hol G) :=
  known (F:=F) B 0 i h A (Push.Local.kappa U z) (Real.sqrt_pos.mpr (force_pos ..))

-- common Raw.Light maps on the paid subspace only
structure Binding {V : Type*} [AddCommGroup V] [Module ℂ V] (K : V → Push.Local.Raw F n) : Prop where
  seed : IsLinearMap ℂ (fun v => (K v).seed)
  bulk i : IsLinearMap ℂ (fun v => (K v).bulk i)
  forced : IsLinearMap ℂ (fun v=> (K v).forced)

-- Projection, residual, rebate etc, exactly Local output. Need Sums before deriving *even formal linearity*.
variable {T : SectionData F} {A : Hol G} {R : Rep G n}



section
open Next.Foundations
open Push.Local.Raw
variable {o : Site n} {X : ℕ → Support n} {w : ℝ}

variable {V : Type*} [AddCommGroup V] [Module ℂ V] {K : V → Raw F n}

private theorem linear_tsum (u : V → F.Coeff) (hu : IsLinearMap ℂ u) (r : V → ℕ → F.Coeff)
    (hr : ∀ i, IsLinearMap ℂ (fun v => r v i)) (hs : ∀ v, Summable (r v)) : IsLinearMap ℂ (fun v => u v + ∑' i, r v i) := by
  constructor
  · intro x y; simp_rw [(hr _).map_add x y,hu.map_add x y,(hs x).tsum_add (hs y),add_add_add_comm]
  intro z x; simp_rw [(hr _).map_smul z x,hu.map_smul z x,(hs x).tsum_const_smul,smul_add]

private theorem linear_forced (f : V → ℕ → Config G n → ℂ) (q : V → ℕ → Config G n → ℂ)
    (p : (ℕ → Config G n → ℂ) →ₗ[ℂ] ℕ → Config G n → ℂ) (hf : IsLinearMap ℂ f) (hq : IsLinearMap ℂ q) : IsLinearMap ℂ (fun v => f v + p (q v)) :=
  ((IsLinearMap.mk' _ hf) + p.comp (IsLinearMap.mk' _ hq)).isLinear

private theorem rows_linear (h : Readable A T R.p n w) (hl : Binding K) (hf : ∀ v, (K v).Format o X R) (i : ℕ) : IsLinearMap ℂ (fun v => (K v).row o X A R.p.threshold i) := by
  let t := R.p.threshold
  let r v := (K v).row o X A t
  have hr (i) : IsLinearMap ℂ (fun v => r v i) := by
    constructor
    · intro x y; dsimp only [r,row,weighted]; rw [(hl.bulk i).map_add x y,project_add A o ((hf x).regular _) ((hf y).regular _) h.order,map_add,map_add]
    intro z x; dsimp only [r,row,weighted]; rw [(hl.bulk i).map_smul z x,project_smul A o _ ((hf x).regular _) h.order,map_smul,map_smul]
  exact hr i

private theorem residual_linear (h : Readable A T R.p n w) (hl : Binding K) (hf : ∀ v, (K v).Format o X R) : IsLinearMap ℂ (fun v i => residual A T o (X i) R.p.threshold ((K v).bulk i)) := by
  let t := R.p.threshold
  let r v := (K v).row o X A t
  have hr (i) : IsLinearMap ℂ (fun v => r v i) := rows_linear h hl hf (o:=o) i
  let g (x : V) (i : ℕ) := residual A T o (X i) t ((K x).bulk i)
  let q (x : V) (i : ℕ) := rebate A T o (X i) t ((K x).bulk i)
  have hg : IsLinearMap ℂ g := by
    constructor
    · intro x y; funext i; change (K (x+y)).bulk i - presented T o t (r (x+y) i) = g x i + g y i
      rw [(hl.bulk i).map_add x y,(hr i).map_add x y,map_add]; exact add_sub_add_comm ..
    intro z x; funext i; change (K (z • x)).bulk i - presented T o t (r (z • x) i) = z • g x i
    rw [(hl.bulk i).map_smul z x,(hr i).map_smul z x,map_smul, ← smul_sub]; rfl
  exact hg

private theorem rebate_linear (h : Readable A T R.p n w) (hl : Binding K) (hf : ∀ v, (K v).Format o X R) : IsLinearMap ℂ (fun v i => rebate A T o (X i) R.p.threshold ((K v).bulk i)) := by
  let t := R.p.threshold
  let r v := (K v).row o X A t
  have hr (i) : IsLinearMap ℂ (fun v => r v i) := rows_linear h hl hf (o:=o) i
  let g (x : V) (i : ℕ) := residual A T o (X i) t ((K x).bulk i)
  let q (x : V) (i : ℕ) := rebate A T o (X i) t ((K x).bulk i)
  have hg := residual_linear h hl hf (o:=o)
  have hq : IsLinearMap ℂ q := by
    have he (v i) : q v i = maskLinear t (X i) ((K v).bulk i) - primary T o t (r v i) - maskLinear t (joint T o (X i)) (g v i) := rfl
    constructor
    · intro x y; funext i; change IsLinearMap ℂ g at hg; simp only [Pi.add_apply,he,(hl.bulk i).map_add x y,(hr i).map_add x y,hg.map_add x y,map_add]; abel
    intro z x; funext i; change IsLinearMap ℂ g at hg; simp only [Pi.smul_apply,he,(hl.bulk i).map_smul z x,(hr i).map_smul z x,hg.map_smul z x,map_smul,smul_sub]
  exact hq

/-- The common-support convention is enforced in the TYPES. -/
private theorem build_linear (S : Slots R.activities (fun i => joint T o (X i))) (h : Readable A T R.p n w) (hl : Binding K) (hf : ∀ v, (K v).Format o X R)
    (hs : ∀ v, Summable ((K v).row o X A R.p.threshold)) :
    let P := fun v => (K v).build o X A T R S
    IsLinearMap ℂ (fun v => (P v).x) ∧ IsLinearMap ℂ (fun v => (P v).regular) ∧ IsLinearMap ℂ (fun v => (P v).forced) ∧ ∀ v, (P v).support=(P 0).support := by
  let t := R.p.threshold
  let r v := (K v).row o X A t
  have hr (i) : IsLinearMap ℂ (fun v => r v i) := rows_linear h hl hf (o:=o) i
  let g (x : V) (i : ℕ) := residual A T o (X i) t ((K x).bulk i)
  let q (x : V) (i : ℕ) := rebate A T o (X i) t ((K x).bulk i)
  have hg := residual_linear h hl hf (o:=o)
  have hq := rebate_linear h hl hf (o:=o)
  have same (v) : ((K v).build o X A T R S).support = fun i => joint T o (X i) := rfl
  exact ⟨linear_tsum _ hl.seed r hr hs, hg, linear_forced _ q (S.packLinear t) hl.forced hq, fun v => (same v).trans (same 0).symm⟩

end

-- common step job, support shape pre-sweep. λ context W.Source histories for all d≥4 at once. prices using same Local conversion Stocks;
-- below canonical projection gate. Repeat at *m common clock* with reserves independent of Period.
section
variable {H0 : RG.History G}

structure Ink (H0 : RG.History G) (N p : ℕ) where
  raw (i : ℕ) : ℕ → Support (H0.S.side i p)
  anchored i j : 0 ∈ raw i j
  cover : WardBin.Gas.Pad (H0.rep N p N).activities (H0.rep N p N).p

-- already can buy separately from `Pads` on our padded history. Supply doesn't require summing unused storage widths nor resetting `W.clock.clip.direct`
abbrev Ink.roles (D : Ink H0 N p) (i : ℕ) (U : SectionData F) := fun j => joint U (0:Site (H0.S.side i p)) (D.raw i j)

variable (D : Ink H0 N p) (S : SectionData F) (A : Hol G)

lemma stakeholders (i j) : 0 ∈ D.roles i S j := Finset.mem_union_left _ (D.anchored i j)

def Users (i : ℕ) := Client (F:=F) H0 (H0.S.side i p) (H0.rep N p i) (D.roles i S) (stakeholders D S i) i A

def Meeting (i : ℕ) (v : Baton F (H0.S.side i p)) (t : ℝ) :=
    let P := castAt (D.roles i S) v
    P.Format 0 A (H0.rep N p i) ∧ P.remBound 0 (H0.rep N p i) (Push.Local.kappa H0 i) t
lemma invited {i : ℕ} {v : Baton F (H0.S.side i p)} : v∈ Users D S A i ↔ ∃ t, Meeting D S A i v t := by
  change (_ ∧ ∃ _, _) ↔ _; exact exists_and_left.symm

-- Hypotheses per-statement and choices M!(j,v) for lifetime. Constructor obligations *not* axiomatized. May use Sector kernel steps or
-- any recipe against our exact Raw, meeting entrance p.fitted and projection + Haar; rendering on R~ rather than SAME R and histories not allowed.
-- In Presolver, choose S.Page rods from available aperture all native shapes, look up costs, increases across β, derivative order. Leading error through Models
-- remains to be proven, Port Γ Pack will ask it literally on Requested. pricing re-check wrappers further below.
structure Goods (l : ℕ) where
  yields (i : ℕ) : l ≤ i → i < N → ↑(Users D S A (i+1)) → Raw F (H0.S.side i p)
  reserve (i : ℕ) : l ≤ i → i < N → Slots (H0.rep N p i).activities (D.roles i S)

structure RawBills {W : Worth} (P : Goods D S A l) (w : ℕ → ℝ) : Prop where
  output (i : ℕ) (hl : l ≤ i) (hi : i < N) (v : Users D S A (i+1)) : ∀ t, Meeting D S A (i+1) v.val t →
    ∃ σ b q ε:ℝ, Prices A S H0 i W (w i) σ b q ε ∧ Output A S H0 N p i 0 (castAt (D.roles (i+1) S) v.val) t
      (D.raw i) (P.yields i hl hi v) σ b q ε
  stock (i : ℕ) : l ≤ i → i ≤ N → Readable A S (H0.rep N p i).p (H0.S.side i p) (w i)
  currency (i : ℕ) : l ≤ i → i < N → hitWidth (H0.levels.budget i)*Push.Local.kappa H0 i ≤ 1
  honors (i : ℕ) (hl : l ≤ i) (hi : i<N) : Binding (P.yields i hl hi)
  same (i : ℕ) : l ≤ i → i ≤ N → H0.Conv N p i -- actual from Selected
  enough : l≤N

private lemma depth_home (i p : ℕ) : (H0.levels.clock.op i p).ratio.parent 0 = 0 := by
  let r := (H0.levels.clock.op i p).ratio
  exact (show r.embed 0 = 0 from r.root.map_zero) ▸ r.embed_parent 0

abbrev delivered (X : Goods D S A l) (i : ℕ) (h₁ : l ≤ i) (he : i < N) (v : ↑(Users D S A (i+1))) :=
  (X.yields i h₁ he v).build 0 (D.raw i) A S (H0.rep N p i) (X.reserve i h₁ he)

variable {W : Worth} {P : Goods D S A l} {w : ℕ → ℝ}

lemma usable (h : RawBills D S A P w (W:=W)) (i : ℕ) (hl : l ≤ i) (hn : i<N) :
    ∃ f : Baton F (H0.S.side (i+1) p) →ₗ[ℂ] Baton F (H0.S.side i p),
    (∀ (v : Users D S A (i+1)),castAt (D.roles i S) (f v.val) = delivered D S A P i hl hn v) ∧
    ∀ (v : Baton F (H0.S.side (i+1) p)) (r : ℝ), Meeting D S A (i+1) v r →
      let Y:= castAt (D.roles i S) (f v)
      let V:= castAt (D.roles (i+1) S) v
      (Y.density 0 S (H0.rep N p i) = ((H0.S.block i).val : ℂ)^d • (H0.levels.clock.op i p).push (H0.β N p (i+1)) (V.density 0 S (H0.rep N p (i+1)))) ∧
      ∃ t, Meeting D S A i (f v) t ∧ direction H0 W i F Y.x V.x t r := by
  let U := Users D S A (i+1)
  let M := P.yields i hl hn
  let o : Site (H0.S.side i p) := 0
  let a := H0.levels.clock.op i p
  have hf := h.stock i hl hn.le
  have hconv := h.same i hl hn.le
  have hw := h.currency i hl hn
  have h0 : a.ratio.parent 0=0 := depth_home ..
  have H (v : U) : (M v).Format o (D.raw i) (H0.rep N p i) ∧ Summable ((M v).row o (D.raw i) A (H0.rep N p i).p.threshold) := by
    obtain ⟨b,hb⟩:= (invited D S A).mp v.property; obtain ⟨u,c,Q,d,hh,hr⟩:= h.output i hl hn v b hb
    have he := Raw.dominated_pieces _ hf hr.raw (hr.income hh (WardBin.rem_nonneg hb.2) hconv hf hw) |>.1.of_norm
    dsimp only [a] at h0
    simpa only [M,h0,o] using And.intro hr.raw he
  let Z := P.reserve i hl hn
  let f₀ := delivered D S A P i hl hn
  obtain ⟨hk,hK,hJ,-⟩:= build_linear Z hf (h.honors i hl hn) (fun i => (H i).1) (fun i=> (H i).2)
  let M0 : U →ₗ[ℂ] Baton F (H0.S.side i p) := LinearMap.prod (IsLinearMap.mk' (fun v : U=>(f₀ v).x) hk)
    (LinearMap.prod (IsLinearMap.mk' (fun v : U=>(f₀ v).regular) hK) (IsLinearMap.mk' (fun v : U=>(f₀ v).forced) hJ))
  obtain ⟨g,hg⟩ := U.subtype.exists_leftInverse_of_injective U.ker_subtype
  let f := M0.comp g
  have he (v : U) : f v.val = WardBin.raw (f₀ v) := by change M0 (g (U.subtype v)) = _; rw [show g (U.subtype v)=v from LinearMap.congr_fun hg v]; rfl
  have hm (v : U) : castAt (D.roles i S) (f v.val)=f₀ v := by rw [he]; rfl
  refine ⟨f,hm,fun v r hr => ?_⟩
  let v' : ↑U := ⟨v,(invited D S A).mpr ⟨r,hr⟩⟩
  let V:= castAt (D.roles (i+1) S) v
  obtain ⟨σ,b,q,ε,hBill,hOut⟩ := h.output i hl hn v' r hr
  have ht (Z : Slots (H0.rep N p i).activities (fun j => joint S (a.ratio.parent 0) (D.raw i j))) := Push.Local.one_step hOut hBill (WardBin.rem_nonneg hr.2) Z (h.same i hl hn.le) hf hw
  dsimp only at ht; dsimp only [a] at h0; rw [h0] at ht
  obtain ⟨h1,h2,h3,h4⟩ := ht Z
  refine ⟨?_,nextCash H0 F i W (castAt (D.roles (i+1) S) v'.val).x r,?_,?_⟩
  · exact hm v' ▸ h3
  · unfold Meeting; dsimp only; rw [show castAt (D.roles i S) (f v) = _ from hm v']; exact ⟨h1,h2⟩
  rw [show castAt (D.roles i S) (f v) = _ from hm v']; exact h4.1

-- Must install SAME resulting flow on Z.flight; this theorem leaves the exact build applicational identities.
-- NOT `stipend smul`: ℓ costs import for Fields/cutoff still needed.
def pageConsole (P : Goods D S A l) (W : Worth) {w} (h : RawBills D S A P w (W:=W)) : WardBin.Console H0 p F where
  rods i := D.roles i S
  centers _ := 0
  flow i := if e : l ≤ i ∧ i < N then Classical.choose (usable D S A h i e.1 e.2) else 0



-- Alternate spins request via pre-export histories: literal built rows in the Motion trees,
-- without introducing Console or Terminal/Transfer normalized data in the prompt. Advantage that can use Local.build_pull orientation if M choices proven covariant (or Walton.Deriv).
-- For now assume spins *of only those raw x*: requires accounting, not derived here.
-- Uses definally arbitrary nonlinear choices outside auth cone but repays on all valid inputs.
def Charges (P : Goods D S A l) : (i : ℕ)→ Baton F (H0.S.side (i+1) p)→ Baton F (H0.S.side i p) := open scoped Classical in fun i x =>
  if h:l ≤ i ∧ i<N then if he : x∈ Users D S A (i+1) then WardBin.raw (delivered D S A P i h.1 h.2 ⟨x,he⟩) else 0 else 0

def entries (i : ℕ) (P : Goods D S A l) (v : Baton F (H0.S.side N p)) : Baton F (H0.S.side i p) := if he : i ≤ N then Nat.decreasingInduction (n:=N) (motive:=fun i _=>Baton F (H0.S.side i p)) (fun i _=>Charges D S A P i) v he else 0





section
open Next.Foundations
variable (E : Bay.Roads G) (p0 : Goods D (localSection G d) (hol G) l) {hG : RG.History G}
structure RawEarned (W : Worth) (w : ℕ→ℝ) : Prop where
  receipts : RawBills D _ _ p0 w (W:=W)
  fit (x : ((frames G).level d).Coeff) : pennies (localSection G d) D.cover (E.art d).cover 0 0 x∈ Users D (localSection G d) (hol G) N
  ink : D.raw N 0 = footprint (E.art d).cover (0 : Site (H0.S.side N p))
  predicted (x : ((frames G).level d).Coeff) :
    let p x := (entries D (localSection G d) (hol G) l p0 (pennies (localSection G d) D.cover (E.art d).cover 0 0 x)).1
    p (star x) = star (p x) ∧ ∀ s : Signed,p (((frames G).level d).act s.ortho x) = ((frames G).level d).act s.ortho (p x)
-- `fit` can and should be obtained from Pennies.Price & groceries, using same Born.One Carry instead of assuming. Need this to use predicts, not spins on admissibles with
-- terminals or free output!




end
end
end YM.Further.PhysicalPeriodLimitF933.Sectioning
