import YM.Bid.Fetch
import YM.Next.FOUNDATIONS.Primary
import YM.Next.FOUNDATIONS.SU2
import YM.Push.PRICE_COMPILER.Basic
import YM.Work.F06
import YM.Work.F07
import YM.Work.F08
import YM.Work.F09

/-!
# Price raw-kernel estimates before L (conditional services)

Raw INPUT ESTIMATES, not claiming their proof: e.g., `FlatBill.Estimates`.
These concern actual Horizon kernel rows in the normalization of
`YM.PREC.Stacks`. Includes harmonic cases, ALL periods as specified by Rack.
Compiles their symbolic bounds. In addition, cost the *repair* on the path to
Teller before L. Allow costing it BEFORE `clip.relaxation` (and the whole
Stage/Sheet); it need only see the direct coefficient and kernel choice. This
is useful to avoid a quantifier trap: consumers might need repair width/data
to set the path widths which in turn need reciprocal-size R0 (`slow_selector`).

Use existing F-services. `pin_before_relaxation` below is a strengthening of
`YM.Bid.pinning`, following that proof with credit independent of the rest
of Stage. We don't construct new F-services here. In particular
widths in a `FlatBill` must not be retroactively changed based on L/levels
or chosen too late for pinning.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Push.PriceCompiler
open Filter Function Lattice RG Wilson Precision Tree Exterior Bloch Laurent Pressure Craft Bid
open scoped Topology Matrix.Norms.Frobenius BigOperators InnerProductSpace

variable {G : Gauge}

lemma strip_mono {α β : Type*} {R : Row α β} {p q A B : ℝ} (h : R.strip p A) (he : q ≤ p) (ha : A ≤ B) :
    R.strip q B := fun i j => (h i j).mono he ha

lemma covered_mono {W : Bed} {p q A B : ℝ} (h : W.covered p A) (he : q ≤ p) (ha : A ≤ B) :
    W.covered q B := by
  obtain ⟨h₁,h₂,h₃,h₄,h₅⟩ := h
  exact ⟨strip_mono h₁ he ha, strip_mono h₂ he ha, strip_mono h₃ he ha, strip_mono h₄ he ha, strip_mono h₅ he ha⟩

lemma numeric_mono {ι : Type*} [Fintype ι] {M : Matrix ι ι ℝ} {a A b B : ℝ}
    (h : Numeric M a A) (hl : b ≤ a) (hr : A ≤ B) : Numeric M b B := by
  intro v
  have hv : 0 ≤ dotProduct v v := Finset.sum_nonneg fun i _ => mul_self_nonneg _
  exact ⟨(mul_le_mul_of_nonneg_right hl hv).trans (h v).1, (h v).2.trans (mul_le_mul_of_nonneg_right hr hv)⟩

lemma floor_mono {M : Bed} {p : Clip} {n : Side} {a A b B : ℝ} (h : Floor M p n a A) (hl : b ≤ a) (hr : A ≤ B) :
    Floor M p n b B := { h with uniform := ⟨numeric_mono h.uniform.1 hl hr, numeric_mono h.uniform.2 hl hr⟩ }

lemma donate_mono {L : Side} {T : Towers L} {K : ℕ} {p q A B : ℝ}
    (h : Donate T p A K) (hl : q ≤ p) (hr : A ≤ B) : Donate T q B K := fun l hK =>
  ⟨strip_mono (h l hK).1 hl (div_le_div_of_nonneg_right hr (by positivity)),
   strip_mono (h l hK).2 hl (div_le_div_of_nonneg_right hr (by positivity))⟩

lemma deep_mono {L : Side} {T : Towers L} {K : ℕ} {p q A B : ℝ}
    (h : T.Deep p A K) (hl : q ≤ p) (hr : A ≤ B) : T.Deep q B K := by
  obtain ⟨h₁,h₂,h₃,h₄⟩ := h
  exact ⟨strip_mono h₁ hl hr, strip_mono h₂ hl hr,
    strip_mono h₃ hl (div_le_div_of_nonneg_right hr (by positivity)), donate_mono h₄ hl hr⟩

lemma reaches_mono {M : C3} {a b : ℝ} (h : Reaches M a) (hl : b ≤ a) : Reaches M b := by
  intro p hp
  refine ⟨(h p hp).1, fun x => le_trans ?_ ((h p hp).2 x)⟩
  exact mul_le_mul_of_nonneg_right hl (Work.F06.sqLength_nonneg _)

/-- A pre-L quote for a part of the kernel input. -/
structure FlatBound where
  width : ℝ
  price : ℝ
  lower : ℝ
  width_pos : 0 < width
  price_pos : 0 < price
  lower_pos : 0 < lower

/-- May be given even for each transition separately: not substituting
next stage's already-*combined* upper constants into this quote. -/
structure FlatBill where
  level : ℕ → FlatBound
  send : ℕ → ℕ → FlatBound  -- arguments (fine-stage j, its output)

/-- Condition on the very same raw Horizon. Along one a these contracts
quantify over all earlier blocking depth, and use universal input rates.
Producing at these quotes later (e.g., after some ADDITIONAL pre-L floor
for the kernel, works for every qualifying Rolls) is required of kernel
work; no price tacitly awarded. -/
structure FlatBill.Estimates (Q : FlatBill) (a : Levels G) (B : Horizon a) : Prop where
  covers N m : m ≤ N → let r := Q.level (a.clock.J m); (B.H N m).covered r.width r.price
  trace N m : m ≤ N → let r := Q.level (a.clock.J m); ∀ n, Floor (B.H N m) (a.params m).clip n r.lower r.price
  oath N m n : m ≤ N → Sworn (B.H N m) n G
  top N n : (B.H N N).diagonal.acts n=1
  crosses N m p : m < N → Towers.Diagonal (a.clock.op m p) (B.H N (m+1)) (B.H N m) (B.towers N m)
  give N m : m < N →
    let j := a.clock.J (m+1)
    let r := Q.send j (a.clock.J m)
    Donate (B.towers N m) r.width r.price (j-2)
  creak N m : m < N →
    let r := Q.send (a.clock.J (m+1)) (a.clock.J m)
    ∃ P : C3, P.strip r.width r.price ∧ Reaches P r.lower ∧ ∀ p,
      Bleeps (a.clock.op m p).ratio (B.H N (m+1)) (B.H N m) (B.towers N m) a.clock.kernel.penalty P

/-- Compile the advertised pair estimates into a monotone convention for Rack. -/
def FlatBill.prices (Q : FlatBill) : MapPrices where
  α := rateLo (fun j => min (Q.level j).width (fromMin (fun j i => (Q.send j i).width) j))
  η := rateLo (fun j => min (Q.level j).lower (fromMin (fun j i => (Q.send j i).lower) j))
  Ω := payHi (fun j => max (Q.level j).price (fromMax (fun j i => (Q.send j i).price) j))
  alpha_pos := rateLo_pos fun j => lt_min (Q.level j).width_pos (lt_min (Q.send ..).width_pos (Q.send ..).width_pos)
  eta_pos := rateLo_pos fun j => lt_min (Q.level j).lower_pos (lt_min (Q.send ..).lower_pos (Q.send ..).lower_pos)

/-- Rate order in which *weaker* budgets suffice. -/
structure Softens (P Q : MapPrices) : Prop where
  width : P.α ≤ Q.α
  price : Q.Ω ≤ P.Ω
  lower : P.η ≤ Q.η

structure KernelMonotone (P : MapPrices) : Prop where
  width : Antitone P.α
  price : Monotone P.Ω
  lower : Antitone P.η
  positive j : 0 < P.Ω j



lemma FlatBill.Estimates.rack {Q : FlatBill} {a : Levels G} {B : Horizon a} (h : Q.Estimates a B) :
    Rack a Q.prices B := by
  let s := fun j i => Q.send j i
  let g := fun j => min (Q.level j).width (fromMin (fun j i => (s j i).width) j)
  let e := fun j => min (Q.level j).lower (fromMin (fun j i => (s j i).lower) j)
  let p := fun j => max (Q.level j).price (fromMax (fun j i => (s j i).price) j)
  have hi j i (h : StepStages j i) : rateLo g j ≤ (s j i).width ∧
      (s j i).price ≤ payHi p j ∧ rateLo e j ≤ (s j i).lower :=
    ⟨(rateLo_le g j).trans ((min_le_right ..).trans (fromMin_le (fun j i => (s j i).width) h)),
      (le_max_of_le_right (le_fromMax (fun j i => (s j i).price) h)).trans (le_payHi p j),
      (rateLo_le e j).trans ((min_le_right ..).trans (fromMin_le (fun j i => (s j i).lower) h))⟩
  refine ⟨fun N m hm => covered_mono (h.covers N m hm) ((rateLo_le g _).trans (min_le_left ..))
    ((le_max_left ..).trans (le_payHi p _)), fun N m hm n => floor_mono (h.trace N m hm n)
      ((rateLo_le e _).trans (min_le_left ..)) ((le_max_left ..).trans (le_payHi p _)), h.oath,
    h.top, fun N m hm => donate_mono (h.give N m hm) (hi _ _ (step_paid a m)).1 (hi _ _ (step_paid a m)).2.1,
    h.crosses, fun N m hm => ?_⟩
  obtain ⟨Y,hp,hr,H⟩ := h.creak N m hm
  obtain ⟨hw,hf,hg⟩ := hi _ _ (step_paid a m)
  exact ⟨Y,strip_mono hp hw hf,reaches_mono hr hg,H⟩

/-- The ex ante K for both Horizon and Teller use. -/
def Pins (P : ℕ → Clip) (r : KernelChoices) (X Y : MapPrices) (G : Gauge) : Prop :=
  ∀ A : Levels G, (∀ m, (A.params m).clip.direct = (P (A.clock.J m)).direct) → A.clock.kernel = r →
    ∀ B : Horizon A, Rack A X B → ∃ T : Horizon A, Retained T B ∧ T.Suffices Y

lemma full_direct {p q : Clip} (hp : p.direct=q.direct) (H : Bed) (n : Side) : H.full p n = H.full q n := by
  rw [Bed.full,Bed.full,hp]

lemma replaces_direct {c f : Side} {g : Ratio c f} {H H' : Bed} {p q x y : Clip} {k : ℝ} {A : C3} {S T : Towers g.count}
    (h : Replaces g H H' p q k A S T) (hp : p.direct=x.direct) (hq : q.direct=y.direct) :
    Replaces g H H' x y k A S T := by
  obtain ⟨h1,h2,h3,h4,h5⟩ := h
  unfold bond at h5
  rw [full_direct hp, full_direct hq] at h3
  rw [full_direct hq] at h4 h5
  exact ⟨h1,h2,h3,h4,h5⟩

/-- Strengthening for price ordering: even if path width requirements
need this K (post-repair widths/exponents etc), can choose them before
R0 (`clip.relaxation`). Clip P argument in this version can have any
provisional relaxation. Only the **direct** coefficient is committed in
the F-cut. All other clip consumers (e.g., Testing.query) must still
be matched to the actual *whole* Clip when used. -/
theorem pin_before_relaxation (r : KernelChoices) (P : ℕ → Clip) (Q : MapPrices) (G : Gauge) :
    ∃ K : MapPrices, Softens K Q ∧ KernelMonotone K ∧ Pins P r Q K G := by
  classical
  -- same algebraic plan as existing Bid.pinning, instantiate F08
  -- on provisional clips. Don't yet even require a `Stage` structure.
  choose w e v hw hv H using fun i : ℕ => Work.F06.answer
    (Q.Ω i) (Q.η i) (Q.α i) (Q.eta_pos i) (Q.alpha_pos i)
  choose y X z hy hz H' using fun i : ℕ => Work.F07.answer (TypeFace 3)
    (e i) (w i) (v i) (hw i) (hv i)
  -- here even t,u have arguments (j finer stage, i coarser stage)
  choose t u ht I using fun j i : ℕ => Work.F08.answer (P j) (P i) r.penalty (Q.Ω j) (Q.α j) (Q.α i)
    (Q.Ω i) (z j) (X j) (j-2) r.penalty_pos (Q.alpha_pos j) (Q.alpha_pos i) (hz j)
  let f (j : ℕ) := min (Q.α j) (fromMin t j)
  let g (j : ℕ) := max (Q.Ω j) (fromMax u j)
  let K : MapPrices := ⟨rateLo f, payHi g, rateLo Q.η,
    rateLo_pos (fun j => lt_min (Q.alpha_pos j) (lt_min (ht ..) (ht ..))), rateLo_pos Q.eta_pos⟩
  have hk : Softens K Q := ⟨fun i => (rateLo_le f i).trans (min_le_left ..),
    fun i => (le_max_left ..).trans (le_payHi g i), rateLo_le _⟩
  refine ⟨K, hk, ⟨rateLo_anti _,payHi_mono _,rateLo_anti _, payHi_pos _⟩, fun A he hb B R => ?_⟩
  have hm (N i : ℕ) : ∃ T : Towers (A.S.block i), i < N →
      let S := B.towers N i; let j := A.clock.J (i+1); let W := B.H N (i+1); let Y := B.H N i
      T.Deep (K.α j) (K.Ω j) (j-2) ∧ T.A0=S.A0 ∧ T.T=S.T ∧ ∀ p : ℕ,
        Towers.Diagonal (A.clock.op i p) W Y T ∧ Towers.Roll (A.clock.op i p) W Y T (A.params (i+1)).clip (A.params i).clip := by
    by_cases Hn : i<N
    · let j := A.clock.J (i+1)
      let k := A.clock.J i
      have hs : StepStages j k := step_paid A i
      obtain ⟨Y,hY,g1,g2⟩ := R.creak N i Hn
      obtain ⟨M,hr,hM,hQ⟩ := H _ Y g1 hY
      obtain ⟨M',hn,hM',hSq⟩ := H' _ M hM hr
      let l := A.S.block i
      obtain ⟨T,hF,hT⟩ := I j k (B.H N (i+1)) (B.H N i) (R.covers _ _ Hn) (R.covers _ _ Hn.le)
        _ hM' l (A.S.block_odd i) _ (R.legs N i Hn)
      have hh (p : ℕ) : Replaces (A.clock.op i p).ratio (B.H N (i+1)) (B.H N i) (A.params (i+1)).clip (A.params i).clip
          (A.clock.op i p).kernel.penalty M' (B.towers N i) T := by
        rw [show (A.clock.op i p).kernel = r from hb]
        exact replaces_direct (hT _ _ _) (he _).symm (he _).symm
      refine ⟨T,fun _ => ⟨deep_mono hF ((rateLo_le f _).trans ((min_le_right ..).trans (fromMin_le t hs)))
        ((le_max_of_le_right (le_fromMax u hs)).trans (le_payHi g _)),
        (hh 0).first.symm,(hh 0).form.symm, fun p => ⟨?_,?_⟩⟩⟩
      · obtain ⟨h1,h2,h3⟩ := R.crosses N i p Hn
        constructor
        · rw [show T.A0=_ from (hh p).first.symm]; exact h1
        · rw [show T.T=_ from (hh p).form.symm]; exact h2
        rw [show T.A0=_ from (hh p).first.symm, show T.T=_ from (hh p).form.symm]; exact h3
      exact Work.F09.answer _ _ _ _ _ _ _ M' M _ _ _ _ _ _ (hh p) (R.traces _ _ Hn _)
        (R.traces _ _ Hn.le _) (R.crosses _ _ _ Hn) (fun n => (hSq n).1) ((g2 p).trans (hQ _).symm)
    exact ⟨B.towers N i,fun H => False.elim (Hn H)⟩
  choose t hT using hm
  let T := { B with towers := t }
  refine ⟨T,⟨rfl,fun N i ha => ⟨(hT _ _ ha).2.1,(hT _ _ ha).2.2.1⟩⟩,?_⟩
  refine ⟨fun N i hi => covered_mono (R.covers N i hi) (hk.width _) (hk.price _),
    fun N i hi n => floor_mono (R.traces N i hi n) (hk.lower _) (hk.price _),
    fun N i hi => (hT N i hi).1,fun N i p hi => ((hT N i hi).2.2.2 p).1,
    fun N i p hi => ((hT N i hi).2.2.2 p).2, R.top⟩

/-- Use once, with only these arguments; in particular it can be known
when choosing working input and output path widths. -/
def preMap (r : KernelChoices) (P : ℕ → Clip) (Q : FlatBill) (G : Gauge) : MapPrices :=
  (pin_before_relaxation r P Q.prices G).choose

lemma preMap_props (r : KernelChoices) (P : ℕ → Clip) (Q : FlatBill) (G : Gauge) :
    Softens (preMap r P Q G) Q.prices ∧ KernelMonotone (preMap r P Q G) ∧
      Pins P r Q.prices (preMap r P Q G) G :=
  (pin_before_relaxation r P Q.prices G).choose_spec

end YM.Push.PriceCompiler
