import YM.Next.WARD_BIN.Baton
import YM.Work.G08

/-!
Its PSREC over the declared slots (inclusively of
healthy boundaries) and common dictionary are NOT consequences here of
having a scalar step.

The same history exact pushes are required.

This version
doesn't need to charge every location from the same printer, each Console
has offsets.

For Family factory compatibility in Flush, uses origin.

No assuming a propagation bound for matched sources. Pay differences at
full supports in a common dictionary and use direction afresh, with actual ν
SUBTRACTED. Export Woke INCLUDING checked ancestry/coordinates, the
propagations true to that console, and top tags not discarded.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WardBin
open Function Filter Set MeasureTheory Wilson Lattice RG Source Bid Work.G08
open scoped Topology Matrix.Norms.Frobenius BigOperators
variable {G : Gauge} {l m d N p : ℕ} {H : History G} {F : Labels.Frame G d} {Y : Hol G}
    {S : SectionData F} {W : Worth}


abbrev κ (H : History G) (i : ℕ) := Real.sqrt (H.levels.clock.forcedAllowance i)

/-- Datum shared including the alphabet at each step. No assumptions on
junk slots or outside valid bounds. Linearity unaudited physically -- needs a
construction as with the commitments in RPaper. -/
structure Console (H : History G) (p : ℕ) (F : Labels.Frame G d) where
  rods (m : ℕ) : Stripe (H.S.side m p)
  centers (m : ℕ) : Site (H.S.side m p)
  flow (m : ℕ) : Baton F (H.S.side (m+1) p) →ₗ[ℂ] Baton F (H.S.side m p)
namespace Console
variable (T : Console H p F)

abbrev stage (i : ℕ) := castAt (F:=F) (T.rods i)
def ticket (i : ℕ) {N : ℕ} (u : Coefficient F (H.S.side i p)) (Y : Hol G) (c : ℝ) :=
  u.Format (T.centers i) Y (H.rep N p i) ∧ u.remBound (T.centers i) (H.rep N p i) (κ H i) c

/-- Missing *one-step* input. Fixed stripe at each level incl for every
Factory index below. Relative to unnormalized prior, exact scaling. No
claim of physical PSREC here; need e.g. direction at the OWN orders,
not some weaker exponent or fewer derivatives after a step. Covers a
stipulated l..m only. -/
structure Purchases (l m N : ℕ) (W : Worth) (S : SectionData F) (Y : Hol G) : Prop where
  sits : m≤N
  roots i : l ≤ i → i < m → T.centers i=(H.levels.clock.op i p).ratio.parent (T.centers (i+1))
  advances i (hi : l ≤ i) (he : i < m) x t :
    let a := T.stage (i+1) x
    let b := T.stage i (T.flow i x)
    T.ticket (i+1) (N:=N) a Y t →
      b.density (T.centers i) S (H.rep N p i) = ((H.S.block i).val:ℂ)^d • (H.levels.clock.op i p).push (H.β N p (i+1))
        (a.density (T.centers (i+1)) S (H.rep N p (i+1))) ∧ ∃ r,
      T.ticket i (N:=N) b Y r ∧ direction H W i F b.x a.x r t



def play (m i : ℕ) : Baton F (H.S.side m p) →ₗ[ℂ] Baton F (H.S.side i p) := if h : i ≤ m then
  Nat.decreasingInduction (n:=m) (motive:=fun i _ => Baton F (H.S.side m p) →ₗ[ℂ] Baton F (H.S.side i p))
    (fun i _ t => (T.flow i).comp t) LinearMap.id h else 0
lemma above_play (j : ℕ) (x) : T.play j j x=x := by rw [play,dif_pos le_rfl,Nat.decreasingInduction_self]; rfl
lemma to_play (m i : ℕ) (hi : i < m) (x) : T.play m i x=T.flow i (T.play m (i+1) x) := by
  rw [play,dif_pos hi.le,Nat.decreasingInduction_succ_left (m:=i) _ _ hi hi.le]
  rw [play,dif_pos (show i+1 ≤ m from hi)]; rfl

def signal (m : ℕ) (x : Baton F (H.S.side m p)) (i : ℕ) := T.stage i (T.play m i x)
def echo (m i : ℕ) : Baton F (H.S.side m p) →ₗ[ℂ] F.Coeff := (LinearMap.fst ℂ _ _).comp (T.play m i)

lemma first (m : ℕ) (x : Baton F (H.S.side m p)) : T.signal m x m=T.stage _ x := by rw [signal,T.above_play]


lemma seen (h : T.Purchases l m N W S Y) (hm : l ≤ m) (x : Baton F (H.S.side m p)) (t : ℝ)
    (hp : T.ticket m (N:=N) (T.stage m x) Y t) :
    ∃ c : ℕ → ℝ,c m=t ∧ (∀ i,l ≤ i → i ≤ m → T.ticket i (N:=N) (T.signal m x i) Y (c i)) ∧
      ∀ i,l ≤ i → i < m → direction H W i F (T.signal m x i).x (T.signal m x (i+1)).x (c i) (c (i+1)) := by
  have he : T.ticket m (N:=N) (T.signal m x m) Y t := by rw [T.first]; exact hp
  suffices H : ∀ i,l≤ i → i ≤ m → ∃ c : ℕ→ℝ,c m=t ∧ (∀ j,i≤j → j ≤ m → T.ticket j (N:=N) (T.signal m x j) Y (c j)) ∧
      ∀ j,i≤j → j<m → direction H W j F (T.signal m x j).x (T.signal m x (j+1)).x (c j) (c (j+1)) from H l le_rfl hm
  intro i hi hj
  induction hj using Nat.decreasingInduction with
  | self => exact ⟨fun _ => t,rfl,fun _ hg hp => le_antisymm hp hg ▸ he,fun _ hj hk => False.elim ((not_lt.mpr hj) hk)⟩
  | of_succ j hj IH =>
    obtain ⟨c,hc,hP,hB⟩ := IH (by omega)
    have hx : T.stage j _ = T.signal m x j := (congr_arg (T.stage j) (T.to_play m j hj x).symm)
    obtain ⟨s,hS,Hs⟩ := (h.advances j hi hj (T.play m (j+1) x) _ (hP _ le_rfl hj)).2
    refine ⟨Function.update c j s, by rw [Function.update_of_ne hj.ne',hc],fun i hi' hp' => ?_,fun i hi' hp' => ?_⟩
    · rcases eq_or_lt_of_le hi' with hf|hf
      · subst i; rw [← hx,Function.update_self]; exact hS
      rw [Function.update_of_ne hf.ne']; exact hP i hf hp'
    rw [Function.update_of_ne (show i+1≠j by omega)]
    rcases eq_or_lt_of_le hi' with hf|hf
    · subst i; rw [← hx,Function.update_self]; exact Hs
    rw [Function.update_of_ne hf.ne']; exact hB i hf hp'

lemma signal_density (h : T.Purchases l m N W S Y) (x : Baton F (H.S.side m p)) {i : ℕ} (hi : l ≤ i) (he : i < m)
    {t : ℝ} (hp : T.ticket (i+1) (N:=N) (T.signal m x (i+1)) Y t) :
    (T.signal m x i).density (T.centers i) S (H.rep N p i) = ((H.S.block i).val:ℂ)^d •
      (H.levels.clock.op i p).push (H.β N p (i+1)) ((T.signal m x (i+1)).density (T.centers (i+1)) S (H.rep N p (i+1))) := by
  unfold signal; rw [T.to_play m i he]
  exact (h.advances i hi he (T.play _ _ x) _ hp).1

/-- Generic on an intermediate scale, motion tested then subtracted at
common placements. Physical identity of A/B needs their *own* respective
inserted meanings/provenance -- `Woke` MUST be accompanied by actual
signal equality, supplied here. -/
lemma wakes (h : T.Purchases l m N W S Y) (hm : l ≤ m) (A B : Coefficient F (H.S.side m p))
    (ha : A.support=T.rods m) (hb : B.support=T.rods m)
    (hx : T.ticket m (N:=N) A Y ((H.levels.params m).columns*F.coeffSize (F.core A.x))) {w b : ℝ}
    (he : T.ticket m (N:=N) B Y b) (hh : b+F.coeffSize B.x≤ w)
    (ht : T.echo m l (raw A)=T.echo m l (raw B)) :
    ∃ R : Duet H F N p l m,R.voice=T.signal m (raw A-raw B) ∧ R.atPoint=T.centers ∧ R.Woke Y W S w := by
  have hu : T.stage m (raw A-raw B)=stepLess A B := by unfold stage stepLess; rw [ha]
  obtain ⟨t,x,y,z⟩ := T.seen h hm (raw A-raw B)
    ((H.levels.params m).columns*F.coeffSize (F.core A.x)+b) (by rw [hu]; exact ⟨sub_funded (ha.trans hb.symm) hx.1 he.1,
    sub_rem (ha.trans hb.symm) hx.1 he.1 hx.2 he.2⟩)
  refine ⟨⟨T.signal m (raw A-raw B),t,T.centers⟩, rfl,rfl,⟨hm,h.sits⟩,y,h.roots,z,?_,?_,?_⟩
  · intro i hi hj; exact T.signal_density h _ hi hj (y (i+1) (by omega) (by omega))
  · rw [show (T.signal m _ l).x = T.echo m l (raw A-raw B) from rfl, map_sub, ht,sub_self]
  have hv := size_triangle F A.x B.x
  have hb0 := rem_nonneg he.2
  have hg : b ≤ w := (le_add_of_nonneg_right (size_nonneg F _)).trans hh
  change t m ≤ w + (H.levels.params m).columns*(w+F.coeffSize (T.signal m _ m).x)
  rw [T.first,hu,x,add_comm ((H.levels.params m).columns*_)]
  refine add_le_add hg (mul_le_mul_of_nonneg_left ((size_core _ A.x).trans (hv.trans ?_))
    (le_trans zero_le_one (H.levels.params m).columns_ge))
  exact add_le_add ((le_add_of_nonneg_left hb0).trans hh) le_rfl

/-- Actual entries use these slots, follow the same console choices. -/
structure Prints (P : TransferData F H N p) (l : ℕ) : Prop where
  bases i : l ≤ i → i ≤ N → T.centers i=0
  uses i : l ≤ i → i ≤ N → ∀ v,(P.entries i v).support = T.rods i
  enters i : l ≤ i → i<N → ∀ v,raw (P.entries i v)=T.flow i (raw (P.entries (i+1) v))

lemma presses {P : TransferData F H N p} {m i} (h : T.Prints P l) (hi : l ≤ i) (hM : m ≤ N) (he : i ≤ m) v :
    T.play m i (raw (P.entries m v)) = raw (P.entries i v) := by
  induction he using Nat.decreasingInduction with
  | self => rw [T.above_play]
  | of_succ j hj ih => rw [T.to_play m j hj,ih (by omega),h.enters _ hi (hj.trans_le hM)]



def matched (m l : ℕ) {N : ℕ} (P : TransferData F H N p) : Baton F (H.S.side m p) →ₗ[ℂ] F.Coeff :=
  P.terminal.symm.toLinearMap.comp (T.echo m l)


/-- A real difference of signals. Synchronizes with every Factory entry in
this printing. Statement at *fixed offset origin*, through m (may be
intermediate). Estimates full-cone cost, not strong-sales for BOTH; use
`G09` afterwards. `Flush` also relates cutoff densities. -/
lemma discrepancy {P : TransferData F H N p} (h : T.Purchases l m N W S Y) (hm : l ≤ m)
    (hx : T.Prints P l) (hp : P.Based Y S l) (B : Baton F (H.S.side m p)) (w b : ℝ)
    (he : T.ticket m (N:=N) (T.stage m B) Y b) (hw : b + F.coeffSize B.1 ≤ w) :
    let v := T.matched m l P B
    ∃ R : Duet H F N p l m,R.Woke Y W S w ∧ R.atPoint=T.centers ∧
      R.voice=T.signal m (raw (P.entries m v)-B) ∧ ∀ i,l ≤ i → i ≤ m →
      R.voice i=stepLess (P.entries i v) (T.signal m B i) := by
  intro v
  let A := P.entries m v
  have ht : T.echo m l (raw A)=T.echo m l B := by
    rw [echo,LinearMap.comp_apply]; unfold A
    rw [T.presses hx le_rfl h.sits hm v]
    exact (hp.reads v).trans (P.terminal.apply_symm_apply _)
  have hh : T.ticket m (N:=N) A Y ((H.levels.params m).columns*F.coeffSize (F.core A.x)) := by
    unfold ticket; rw [hx.bases m hm h.sits]; exact ⟨hp.format m hm h.sits v,hp.cap m hm h.sits v⟩
  obtain ⟨R,hR,hG,HS⟩ := T.wakes h hm A (T.stage m B) (hx.uses m hm h.sits v) rfl hh he hw (by exact ht)
  refine ⟨R,HS,hG,hR,fun i hi he => ?_⟩
  rw [hR,signal]; change castAt _ (T.play m i (raw (P.entries m v)-B))=_
  rw [map_sub,T.presses hx hi h.sits he]; unfold stepLess; rw [hx.uses i hi (he.trans h.sits)]; rfl

end Console

end YM.WardBin
