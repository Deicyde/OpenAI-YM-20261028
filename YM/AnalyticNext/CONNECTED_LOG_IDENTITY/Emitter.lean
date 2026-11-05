import YM.AnalyticNext.CONNECTED_LOG_IDENTITY.LogAction
import YM.Next.EXTRACTION.Tails
import YM.Next.FOUNDATIONS.SU2
import YM.Org.Theatre


set_option warningAsError false

/-!
# The liberated vacuum formula in the actual RG representation

Choose dictionaries and normalization once. Both the leading log and K
reconnect are countable here even though the lattice is finite. Don't
confuse the denotational K predicates/values with operational semantics:
we retain older predicates from d as V-dependences and can also keep them as
the new `.extraTest`; keep the earlier supports & inventories as record
data in the address decoder. The earlier disjointness and incidence guards
in the values remain EXACTLY those used in the computed charge.

Anchor accounting: species specified by finite *sets* might not have an
equivariant anchor (consider a winding species stabilized by a
translation). Never compute a regular payload by making an arbitrary
translation-dependent tie decision. Here one copy per site of the
clustering tuple's root label, sharing one unit of expense (field values
divided by card root footprint).

Issued *formula*. Also derivatives/asymptotic/secant and calibrated receipt
obligations to use in a Move; see files dependent on this one for some
such costs. No assuming a history producer or asserting the emitted
R is already admissible.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Push.LogIdentity.Emit
open Lattice RG Wilson Pressure Finset Filter Function
open AbsoluteSums Ursell Restore Attach
open scoped BigOperators Topology Classical Matrix.Norms.Frobenius ContDiff
variable {n : Side} {G : Gauge} {ι κ : Type*} (X : ι → Support n) (Y I : κ → Support n)
    (hX : ∀ i,(X i).Nonempty) (hI : ∀ i,(I i).Nonempty) (hQ : ∀ i,I i ⊆ Y i)
    (p : BudgetPoint)

/-- Decoder with separate dummy room *at all sites*, can permute coherently
also on the padding. -/
abbrev Padded (ι : Type*) (n : Side) := ι ⊕ (ℕ × Site n)

def codec (ι : Type*) [Countable ι] (n : Side) : Padded ι n ≃ ℕ :=
  nonempty_equiv_of_countable.some

def padEval {V : Type*} [Zero V] (F : ι → V) (i : Padded ι n) := i.elim F (fun _ => 0)

private def padEmb (ι : Type*) (n : Side) : ι ↪ Padded ι n := ⟨Sum.inl,Sum.inl_injective⟩

lemma pad_absolute (f : ι → ℝ) : Summable (padEval f (n:=n)) ↔ Summable f :=
  ((padEmb ι n).injective.summable_iff (f:=padEval f (n:=n)) (by
    rintro (i|i) h
    · exact (h ⟨i,rfl⟩).elim
    rfl)).symm

lemma pad_total (f : ι → ℝ) : (∑' i : Padded ι n,padEval f i) = ∑' i,f i :=
  ((padEmb ι n).injective.tsum_eq (f:=padEval f (n:=n)) (by
    rintro (i|i) h
    · exact ⟨i,rfl⟩
    exact (h rfl).elim)).symm

-- Can derive from Countable's hypotheses on demand
variable [Countable κ] [Countable ι]

abbrev Anchors := Σ z : Clusters ι, ↥(X (z.2 none))

def share (w : Clusters ι → ℝ) (z : Anchors X) := w z.1/(X (z.1.2 none)).card

include hX in
omit [Countable ι] in
lemma splits (w : Clusters ι → ℝ) (z : Clusters ι) : ∑ i : ↥(X (z.2 none)),share X w ⟨z,i⟩=w z := by
  unfold share; simp only [sum_const,card_univ,Fintype.card_coe,nsmul_eq_mul]
  have he : 0 < ((X (z.2 none)).card : ℝ) := by exact_mod_cast (card_pos.mpr (hX (z.2 none)))
  field_simp

omit [Countable ι] in
lemma norm_share (w : Clusters ι → ℝ) (z : Anchors X) : ‖share X w z‖ = share X (fun i => ‖w i‖) z := by
  simp only [share,norm_div,norm_natCast]

include hX in
omit [Countable ι] in
lemma pays_every (w : Clusters ι → ℝ) (h : Summable fun i => ‖w i‖) :
    Summable (fun i => ‖share X w i‖) ∧ (∑' i : Anchors X,share X w i) = ∑' i,w i := by
  have he : Summable (fun i => ‖share X w i‖) := by
    refine (summable_sigma_of_nonneg (fun i => norm_nonneg (share X w i))).mpr ⟨fun i => Summable.of_finite,?_⟩
    convert h using 1
    ext i; rw [tsum_fintype]; simp_rw [norm_share, splits X hX]
  refine ⟨he,?_⟩
  rw [he.of_norm.tsum_sigma]; apply tsum_congr; intro i; rw [tsum_fintype, splits X hX]

-- New regular addresses

def host (z : Anchors X) : RegularAddress n :=
  ⟨z.2, Z X z.1, Zcontains X z.1 none z.2.property⟩

def table : Padded (Anchors X) n → RegularAddress n :=
  Sum.elim (host X) fun i => ⟨i.2,{i.2},mem_singleton_self _⟩

def reg := table X ∘ (codec (Anchors X) n).symm

def ability (u : Config G n → ι → ℝ) (v : Clusters ι → ℝ) (i : Anchors X) (V : Config G n) :=
  share X (regular X (u V) v) i

def lettering (u : Config G n → ι → ℝ) (v : Clusters ι → ℝ) (i : Padded (Anchors X) n) (V : Config G n) :=
  padEval (fun i => ability X u v i V) i

def E (u : Config G n → ι → ℝ) (v : Clusters ι → ℝ) := lettering X u v ∘ (codec (Anchors X) n).symm

def earned (u : Config G n → ι → ℝ) (v : Clusters ι → ℝ) (V : Config G n) (i : ℕ) :=
  masked p.threshold (reg X i).support (E X u v i) V

def maskedIn (u : Config G n → ι → ℝ) (v : Clusters ι → ℝ) (V : Config G n) :=
  Restore.good (Restore.Z X) (RG.flags p.threshold V) (regular X (u V) v)

lemma earned_eq (u : Config G n → ι → ℝ) (v : Clusters ι → ℝ) (V : Config G n) :
    earned X p u v V = padEval (share X (maskedIn X p u v V)) (n:=n) ∘ (codec (Anchors X) n).symm := by
  funext i; obtain ⟨j,rfl⟩ := (codec (Anchors X) n).surjective i
  unfold earned reg E; simp only [comp_apply, Equiv.symm_apply_apply]; unfold lettering padEval table ability
  rcases j with i|i
  · change masked _ (Z X i.1) _ V = _
    by_cases he : Healthy p.threshold (Z X i.1) V
    · rw [masked_eq _ _ _ _ he]; unfold share maskedIn Restore.good; simp only [Sum.elim_inl,if_pos (show Disjoint _ _ from he)]
    rw [masked_ne _ _ _ _ he]; change 0=share X _ _; unfold share maskedIn Restore.good; rw [if_neg (show ¬ Disjoint _ _ from he),zero_div]
  by_cases he : Healthy p.threshold {i.2} V
  · exact masked_eq _ _ _ V he
  exact masked_ne _ _ _ V he

include hX in
lemma additive_series (u : Config G n → ι → ℝ) (v : Clusters ι → ℝ) (V : Config G n)
    (h : Summable (fun i => ‖maskedIn X p u v V i‖)) :
    Summable (fun i => ‖earned X p u v V i‖) ∧ (∑' i,earned X p u v V i) = ∑' i,maskedIn X p u v V i := by
  rw [earned_eq]; let w := share X (maskedIn X p u v V)
  let e := (codec (Anchors X) n).symm
  obtain ⟨he,hT⟩ := pays_every X hX _ h
  have hD (i : Padded (Anchors X) n) : ‖padEval w i‖=padEval (fun i => ‖w i‖) i := by
    rcases i with i|i; rfl; exact norm_zero
  constructor
  · change Summable ((fun i : Padded (Anchors X) n => ‖padEval w i‖) ∘ e)
    rw [e.summable_iff]; simp_rw [hD]; exact (pad_absolute _).mpr he
  change (∑' i,padEval w (e i)) = _
  rw [Equiv.tsum_eq,pad_total]; exact hT

section Publish
variable (test : κ → Config G n → Prop) -- old forced extra tests (may also all be carried implicitly inside d)

def letterTest (i : Out X Y) (V : Config G n) : Prop :=
  ∀ j∈i.val.val.fst.toLeft,test j V

def stationed (i : Out X Y) : ForcedAddress G n :=
  ⟨location X Y i,flagsOut X Y I i,hold_nonempty Y _ _ i hI,hold_zone Y _ _ i hQ,letterTest X Y test i⟩

def reserve : Padded (Out X Y) n → ForcedAddress G n := Sum.elim
  (stationed X Y I hI hQ test) fun i =>
    ⟨{i.2},{i.2},Finset.singleton_nonempty _,Finset.Subset.refl _,fun _ => False⟩

def forced := reserve X Y I hI hQ test ∘ (codec (Out X Y) n).symm

def imprint (u : Config G n → ι → ℝ) (d : Config G n → κ → ℝ) (v : Clusters ι → ℝ)
    (i : Padded (Out X Y) n) (V : Config G n) :=
  padEval (Restore.K X Y I (RG.flags p.threshold V) (u V) (d V) v) i

def body (u : Config G n → ι → ℝ) (d : Config G n → κ → ℝ) (v : Clusters ι → ℝ) :=
  imprint X Y I p u d v ∘ (codec (Out X Y) n).symm

/-- The raw reconnected activity data with all signs. Not yet
asserting contraction, test-affine Hessian, mask changes etc. -/
def print (u : Config G n → ι → ℝ) (d : Config G n → κ → ℝ) (v : Clusters ι → ℝ) :
    Activities G n := ⟨reg X,forced X Y I hI hQ test,E X u v,body X Y I p u d v⟩

def gasAt (u : Config G n → ι → ℝ) (d : Config G n → κ → ℝ) (v : Clusters ι → ℝ) (V : Config G n) :=
  gasTerm (location X Y) (flagsOut X Y I) (RG.flags p.threshold V)
    (Restore.K X Y I (RG.flags p.threshold V) (u V) (d V) v)

lemma gas_distance (u : Config G n → ι → ℝ) (d : Config G n → κ → ℝ) (v : Clusters ι → ℝ) (V : Config G n) :
    let g := gasAt X Y I p u d v V
    let A := print X Y I hI hQ p test u d v
    (Summable (fun i => ‖A.gasOccurrence p i V‖) ↔ Summable (fun i => ‖g i‖)) ∧
    A.gas p V = ∑' i,g i := by
  intro g A
  let e := (padEmb (Out X Y) n).trans (codec (Out X Y) n).toEmbedding
  let L := fun i => (A.forced i).support
  let M := fun i => (A.forced i).inventory
  let F := fun i => A.K i V
  have he (i) (hi:F i≠0) : i∈Set.range e := by
    obtain ⟨t,rfl⟩ := (codec (Out X Y) n).surjective i
    rcases t with t|t
    · exact ⟨t,rfl⟩
    refine (hi ?_).elim
    change imprint X Y I p u d v ((codec _ _).symm ((codec _ _) (Sum.inr _))) V = 0; rw [Equiv.symm_apply_apply]; rfl
  have hx : (fun s => A.gasOccurrence p s V)=gasTerm L M (RG.flags p.threshold V) F := by
    funext i
    unfold Activities.gasOccurrence gasTerm Records Apart Activities.admissible
    congr!  -- classical guard
  have hL : (fun i => L (e i)) = location X Y := by
    funext i
    change (reserve X Y I hI hQ test ((codec _ _).symm ((codec _ _) (Sum.inl i)))).support = _
    rw [Equiv.symm_apply_apply]; rfl
  have hM : (fun i => M (e i)) = flagsOut X Y I := by
    funext i
    change (reserve X Y I hI hQ test ((codec _ _).symm ((codec _ _) (Sum.inl i)))).inventory = _
    rw [Equiv.symm_apply_apply]; rfl
  have hF : (fun i => F (e i)) = Restore.K X Y I (RG.flags p.threshold V) (u V) (d V) v := by
    funext i
    change imprint X Y I p u d v ((codec _ _).symm ((codec _ _) (Sum.inl i))) V = _
    rw [Equiv.symm_apply_apply]; rfl
  have hz := project_forced e L M (RG.flags p.threshold V) F he
  dsimp only at hz; rw [hL,hM,hF,← hx] at hz; exact hz

/-- Insert the theory's OWN coarse denominator & path choices on
the unnormalized vacuum representation. Here B is LOG of scalar at
this volume (may already include pStep.R.v from the incoming cutoff).
Path/loop normalization and beta calibration are separately required!
-/
def insert (u : Config G n → ι → ℝ) (d : Config G n → κ → ℝ) (v : Clusters ι → ℝ)
    (R : PathData G) (c : Clip) (β B : ℝ) : Rep G n :=
  ⟨R,c,print X Y I hI hQ p test u d v,p,β,(B+∑' i,v i)/(Fintype.card (Site n))⟩

include hX in
lemma recovers (u : Config G n → ι → ℝ) (d : Config G n → κ → ℝ) (v : Clusters ι → ℝ)
    (R : PathData G) (c : Clip) (β B : ℝ) (V : Config G n)
    (h : Summable (fun i => ‖maskedIn X p u v V i‖)) (_hh : Summable (fun i => ‖gasAt X Y I p u d v V i‖)) (_hv : Summable fun i => ‖v i‖) :
    let τ := insert X Y I hI hQ p test u d v R c β B
    τ.eval V = (Real.exp B * Real.exp (-R.inChannels c p β V)) *
      (Real.exp ((∑' i,v i) - ∑' i,maskedIn X p u v V i)*(∑' i, gasAt X Y I p u d v V i)) := by
  intro T
  unfold Rep.eval Rep.exponent T insert
  dsimp only
  rw [(gas_distance X Y I hI hQ p test u d v V).2, Activities.additive]
  change Real.exp (_ - _ - ∑' i,earned X p u v V i) * _ = _
  rw [(additive_series X hX p u v V h).2]
  rw [div_mul_cancel₀ _ (by positivity),← Real.exp_add,← mul_assoc,← Real.exp_add]; congr 2; ring

include hX

end Publish
end YM.Push.LogIdentity.Emit
