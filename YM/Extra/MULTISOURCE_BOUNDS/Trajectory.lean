import YM.Extra.MULTISOURCE_BOUNDS.Rates
import YM.Extra.MULTISOURCE_BOUNDS.Schedule
import YM.Work.A01.Support

/-!
# A sufficient trajectory interface, and commissioning it on all scales

The one-step analytic input `Raw` is a JMara-type absolute
bound at the **provisional**, not repainted, output radii; the polynomial
cost is applied after the full forced divisor. It is not provided by EBare,
Based or exactness. It only needs to apply on the bands actually produced,
for admitted derivative orders/supports. The one-step precondition uses both
sorts of actual nonunit marked terms including singleton section terms and
compensation, *no* absolute smallness of global units at this test. Units are
instead priced separately for evaluation. See `Prepared.projects` for
input mass conversion, not claiming the integration result `Raw` in general.

`Skeleton` and `Unbilled` are INPUTS (esp. to companion trajectory and cutoff
vacuum builders). They do not say that estimates were satisfied along the
run. They require MANY-name structural data and local producer bounds about
the full densities of the same physical products; no labelling of a
polynomial in a different vacuum as though it transferred here. Any
alternate alphabet should justify an appropriate comparison/price theorem or
use modified inputs openly. All eventuality and volume scope of this route
to Center are in Application. More stringent dictionary requirements for
comparisons / noncentered births not passing `Copied`, continuum detector
estimates etc. are not solved here.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Extra.Multi
open Function Filter Lattice RG Source Wilson Overlay Marker Labels MeasureTheory Finset
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical

variable {G : Gauge} {C : Family G} {V : Type*} [DecidableEq V] {R : Census V}
variable {m i N p : ℕ} {s : Scope} {t : Tariff}

/-- Physical step estimate needed between two explicit arrays. This is before
the separation gain and iteration. For a version accepting arbitrary input
couplings/masks replace only if actually established. Small input nonunits
(factorial-free); no positivity of amplitudes. -/
def Raw (C : Family G) (A : Bands R (C.path.rep N p m)) (A' : Bands R (C.path.rep N p (m+1)))
    (D : V→ℕ) (t : Tariff) := ∀ w : V → ℝ, (∀ i, 0<w i) →
      Spent entire A' w 0 (divisor C (m+1)) ((gHat C (m+1))^2/2) →
      Spent mixed A (fun i => w i / scaleFee C m t (D i)) 1 (divisor C m) (quote C m t)

/-- Extra cost at cutoff (or instead build a different birth producer);
`Lawful` alone doesn't assert this strengthened exponent. -/
def Thick (C : Family G) (N p : ℕ) := let P := C.path.rep N p N
    ∃ k : ℕ → ℝ, (∀ i, 0≤k i ∧ ∀ U, ‖P.activities.K i U‖ ≤ k i) ∧
      Ac.Hit (fun i => (P.activities.forced i).support) P.p.B k (P.p.supportExponent+1)
        (C.path.levels.clock.forcedAllowance N)

/-- Protected subset can keep its full rates (at every opening). Pure
coincident pairs require a smaller protected subset or some other argument,
see `coincidence`. Doesn't exclude coincidences/alternatives in the census.
-/
def Fresh {n : Side} (hot : Finset V) (R : Census V) (o : V → Site n) (B : ℕ) := ∀ q : R.Mode,
    (↑(q.val∩hot) : Set V).Pairwise fun x y => B^2 ≤ separation (o x) (o y)

lemma Fresh.packs {n : Side} {B : ℕ} {hot : Finset V} {o : V → Site n} (h : Fresh hot R o B) (hB : 0<B) :
    ∀ i : R.Mode, mixed i → let s := i.val; let y := (s∩hot).image o
      s.Nonempty ∧ ((s∩hot).card ≤ (s\hot).card ∨
        2 ≤ y.card ∧ (↑y : Set (Site n)).Pairwise (fun x y => B^2 ≤ separation x y)) := by
  intro i hi s y
  have hw : 0<B^2 := pow_pos hB _
  change 2 ≤ s.card at hi
  refine ⟨card_pos.mp (by omega),?_⟩
  by_cases hn : (s∩hot).card ≤ (s\hot).card
  · exact Or.inl hn
  have H : Set.InjOn o (s∩hot : Finset V) := by
    intro x hx y hy hxy; by_contra he
    have : _ ≤ separation (o x) (o y) := h i hx hy he
    rw [hxy] at this; simp at this; omega
  refine Or.inr ⟨?_,fun x hx z hz he => ?_⟩
  · have hb : (s∩hot).card + (s\hot).card = s.card := by grind -- card_sdiff
    rw [card_image_of_injOn H]; omega
  obtain ⟨x,hx',rfl⟩ := mem_image.mp (show x∈y from hx)
  obtain ⟨z,hz',rfl⟩ := mem_image.mp (show z∈y from hz)
  exact h i hx' hz' (ne_of_apply_ne _ he)

variable [Fintype V]
variable {D : V → ℕ} {u : ∀ i, C.label (D i)} {r : V→ℝ}
variable (H : C.Makes) (hprep : Prepared s t C.localSection C.path.levels) (hot : Finset V)
  (hr : ∀ i,0<r i) (hc : ∀ i,(C.labels.level (D i)).coeffSize (u i) ≤ r i)

/-- Sufficient tagged canonical cutoff array interface. Use either combined or
separate/disjoint blocks of the original column coordinates for the attaching
letter at each name. Components must visit each participating name exactly
once, regardless of the number of basis terms or other histories at that
name. Zero ghosts permitted subject to `Active` elsewhere. -/
def Opening (C : Family G) (A : Bands R (C.path.rep N p N)) (D : V → ℕ) (u : ∀ i,C.label (D i)) :=
    let Y i := (C.localSection (D i)).footprint (A.origins i)
    Birth A mixed id Y (fun i => canon C N p N (A.origins i) (u i)) ∨
      ∃ slots : ∀ i, PiecesAt (C.labels.level (D i)), (∀ i, Pairwise (Function.onFun Disjoint (slots i))) ∧
        Birth A mixed Prod.fst (fun j : V×ℕ => Y j.1)
          (fun j => portion C N p N (A.origins j.1) (u j.1) (slots j.1 j.2))

include H hprep hr hc in
theorem born_of_fibers {α : Type*} {A : Bands R (C.path.rep N p N)} (h : Thick C N p) (hy : A.Active)
    (hn : ∀ i,C.ref (D i) ≤ N) (hμ : Occupancy A.origins (s.markers (year C N))) {q : α→V}
    {term : α → Config G (C.side N p) → ℂ} (K : α → ℝ) (hK : ∀ i,0 ≤ K i ∧ ∀ U, ‖term i U‖ ≤ K i)
    (hBound : ∀ i, ∀ t : Finset α, (∀ j∈t,q j=i) → (∑ j∈t,K j) ≤
      BasisCost.price (C.localSection (D i)) * (gHat C N)⁻¹^BasisCost.slots (C.labels.level (D i)) * allowance C N p N (u i))
    (hb : Birth A mixed q (fun j => (C.localSection (D (q j))).footprint (A.origins (q j))) term) :
    Spent mixed A (rate C N t hot D r N) 0 (divisor C N) (gHat C N ^ 4) := by
  let g := gHat C N; let κ := divisor C N; let w := rate C N t hot D r N
  obtain ⟨k,hk,hVac⟩ := h
  let P := (C.path.rep N p N).p
  have hp : P = point C N := (H.wilson.represents N p N le_rfl).vac
  let Y i := (C.localSection (D i)).footprint (A.origins i)
  let μ := s.markers (year C N)
  let Z i := BasisCost.price (C.localSection (D i)) * g⁻¹^BasisCost.slots (C.labels.level (D i)) * allowance C N p N (u i)
  have hh := hprep.here N
  change Ample C.localSection _ μ _ (hat C N) at hh
  have he i := hh.atlas (D i) (admitted C N H (hn i))
  change ∀ i, _ ≤ (point C N).B ∧ _ * _ * g ≤ 1 at he
  let F i := C.labels.level (D i)
  let X i := coord C N p N (u i)
  have hZ i := BasisCost.price_pos (C.localSection (D i))
  have hg : 0<g := gHat_pos ..
  have hw i : 0<w i := rate_pos hot (hr i)
  have hz i : (F i).coeffSize ((F i).core (X i).x) ≤ allowance C N p N (u i) := (BasisCost.coeff_le _).trans
    (le_mul_of_one_le_left (BasisCost.coeff_nonneg _) (col_ge C N))
  have Hz i : 0≤allowance C N p N (u i) := (BasisCost.coeff_nonneg _).trans (hz i)
  have HZ i : 0≤Z i := mul_nonneg (mul_nonneg (zero_le_one.trans (hZ i)) (by positivity)) (Hz i)
  have ht i : Real.exp ((P.supportExponent+2)*coverNumber P.B (Y i)) * (w i * Z i) ≤ g^6 := by
    have hx := BasisCost.small_footprint (C.localSection (D i)) (A.origins i) (he i).1
    let price := BasisCost.price (C.localSection (D i))
    have hw' := pays_coord C N p N (hr i) (strength C.labels (D i)) H (u i) (hc i) (hn i) le_rfl
    replace hw' : w i * allowance C N p N (u i) ≤ g ^ (strength C.labels (D i)) :=
      (mul_le_mul_of_nonneg_right (rate_le hot (hr i)) (Hz i)).trans hw'
    have h1 : 0 ≤ P.supportExponent + 2 := by have := P.exponent_pos; linarith
    calc
      _ ≤ Real.exp (P.supportExponent+2) * (w i * Z i) := by
        apply mul_le_mul_of_nonneg_right _ (mul_nonneg (hw _).le (HZ _)); apply Real.exp_monotone
        apply mul_le_of_le_one_right h1
        rw [hp]; exact_mod_cast hx
      _ = Real.exp ((point C N).supportExponent+2) * price * g⁻¹^BasisCost.slots (F i) * (w i * allowance C N p N (u i)) := by
        rw [hp]; unfold Z F price; ring
      _ ≤ Real.exp ((point C N).supportExponent+2)* price * g⁻¹^BasisCost.slots (F i)*g^(strength C.labels (D i)) :=
        mul_le_mul_of_nonneg_left hw' (mul_nonneg (mul_nonneg (Real.exp_pos _).le (zero_le_one.trans (hZ i))) (by positivity))
      _ = (Real.exp ((point C N).supportExponent+2)*price*g)*g^7 := by
        rw [strength,pow_add,inv_pow]; unfold F; field_simp
      _ ≤ _ := (mul_le_of_le_one_left (by positivity) (he i).2).trans (pow_le_pow_of_le_one hg.le (gHat_le_one ..) (by decide))
  have he' : Rooted (fun j => {q j}) (fun j => Y (q j)) P.B (P.supportExponent+1+1) (fun j => w (q j)*K j) (g^6) := by
    intro i
    refine Budget.certify (fun v => ?_) (fun s => ?_)
    · split; exact mul_nonneg (Real.exp_pos _).le (mul_nonneg (hw _).le (hK _).1); rfl
    let s' := s.filter fun j => i=q j
    have hq j (hj : j∈s') : q j=i := (mem_filter.mp hj).2.symm
    simp only [Finset.mem_singleton]; rw [← sum_filter]; apply le_trans ?_ (ht i)
    calc
      ∑ j ∈ s', _ = Real.exp ((P.supportExponent+2)*coverNumber P.B (Y i))*(w i*∑ j∈s',K j) := by
        simp only [mul_sum]; exact sum_congr rfl fun j hj => by rw [hq _ hj]; ring_nf
      _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hBound i s' hq) (hw _).le) (Real.exp_pos _).le
  let γ := μ*siteFactor P.B*(g^6)
  have hγ := root_hit hμ (fun i => mul_nonneg (hw _).le (hK i).1) (pow_nonneg hg.le _)
    (fun i _ => ⟨_,mem_singleton_self _,show A.origins (q i)∈Y (q i) from mem_image.mpr ⟨0,(H.sections _).anchored,by simp⟩⟩) he'
  have hc : 0 ≤ κ+γ := by unfold γ siteFactor; have := divisor_pos C N; dsimp only [κ]; positivity
  have hk0 : κ ≤ g^6 := hh.vacuum
  let B := P.B
  let b : ℝ := ((B+B+1:ℕ):ℝ)^4
  have hb1 : 1 ≤ b := one_le_pow₀ (by exact_mod_cast (show 1 ≤ B+B+1 by omega))
  have hf : (1+μ*siteFactor P.B)*b*g ≤ 1 := by dsimp only [b,B]; rw [hp]; exact hh.contact
  have hsmall : b*(κ+γ) ≤ g^5 := calc
    _ ≤ b*(g^6+γ) := by gcongr
    _ = ((1+μ*siteFactor P.B)*b*g)*g^5 := by unfold γ; ring
    _ ≤ _ := mul_le_of_le_one_left (by positivity) hf
  have Hs : κ+γ ≤ g^5 := (le_mul_of_one_le_left hc hb1).trans hsmall
  have hm : g^5 ≤ 1 := pow_le_one₀ hg.le (gHat_le_one ..)
  have hh := hb.spent mixed hy (fun i => (hw i).le) hk hK (divisor_pos C N) (divisor_le C N)
    (δ:=0) (by simpa using P.exponent_pos.le : 0 ≤ P.supportExponent+0) (a:=κ) (by
      rw [show divisor C N*κ=C.path.levels.clock.forcedAllowance N from (Real.mul_self_sqrt (Real.exp_pos _).le), add_zero]; exact hVac)
    (b:=γ) (by simpa only [add_zero] using hγ) hc (hsmall.trans hm)
  refine hh.mono (fun i => (hw i).le) (fun _ => le_rfl) (divisor_pos ..).le ?_ (fun _ h => h) (fun _ h => h)
  have H1 := (le_abs_self _).trans (Real.abs_exp_sub_one_le (x:=κ+γ) (by rw [abs_of_nonneg hc]; exact Hs.trans hm))
  rw [abs_of_nonneg hc] at H1; have ht : g ≤ 1/4 := (hprep.here N).perturb
  exact H1.trans ((mul_le_mul_of_nonneg_left Hs (by positivity)).trans (by nlinarith [mul_le_mul_of_nonneg_left ht (pow_nonneg hg.le 4)]))

include H hprep hr hc in
lemma born_mixed {A : Bands R (C.path.rep N p N)} (h : Thick C N p) (hy : A.Active)
    (hn : ∀ i, C.ref (D i) ≤ N) (hμ : Occupancy A.origins (s.markers (year C N))) (hb : Opening C A D u) :
    Spent mixed A (rate C N t hot D r N) 0 (divisor C N) (gHat C N ^ 4) := by
  let F i := C.labels.level (D i)
  let g := gHat C N
  let base i := BasisCost.price (C.localSection (D i)) * g⁻¹ ^ BasisCost.slots (F i)
  let X i := (coord C N p N (u i)).x
  have hbase i : 0 ≤ base i := by
    have := BasisCost.price_pos (C.localSection (D i)); have hg : 0 < g := gHat_pos ..; unfold base; positivity
  rcases hb with hb|⟨slots,hslot,hb⟩
  · let K i := base i*(F i).coeffSize ((F i).core (X i))
    refine born_of_fibers H hprep hot hr hc h hy hn hμ K (fun i => ⟨mul_nonneg (hbase _) (BasisCost.coeff_nonneg _), fun U =>
      BasisCost.full_scaled _ _ _ (gHat_pos ..) (gHat_le ..) (gHat_le_one ..) _⟩) (fun i s hs => ?_) hb
    calc
      _ ≤ ∑ j∈({i}:Finset V),K j := sum_le_sum_of_subset_of_nonneg (fun j hj => mem_singleton.mpr (hs j hj))
        (fun j _ _ => mul_nonneg (hbase _) (BasisCost.coeff_nonneg _))
      _ ≤ _ := by rw [sum_singleton]; exact mul_le_mul_of_nonneg_left ((BasisCost.coeff_le _).trans
        (le_mul_of_one_le_left (BasisCost.coeff_nonneg _) (col_ge ..))) (hbase _)
  let cost (i : V) (j : ℕ) := base i * (F i).coeffSize (partialCore (F i) (slots i j) (X i))
  refine born_of_fibers H hprep hot hr hc h hy hn hμ (fun i : V × ℕ => cost i.1 i.2) (fun i => ⟨mul_nonneg (hbase _) (BasisCost.coeff_nonneg _), fun U =>
    BasisCost.full_scaled _ _ _ (gHat_pos ..) (gHat_le ..) (gHat_le_one ..) _⟩) (fun i s hs => ?_) hb
  calc
    _ = ∑ j∈s.image Prod.snd, cost i j := by
      rw [sum_image (show Set.InjOn Prod.snd s from fun a ha b hb h => Prod.ext ((hs a ha).trans (hs b hb).symm) h)]
      exact sum_congr rfl fun j hj => congr_arg (fun k => cost k j.2) (hs j hj)
    _ ≤ _ := by unfold cost; rw [← mul_sum]; exact mul_le_mul_of_nonneg_left ((pieces_sum _ _ (hslot i) _ _).trans
        (le_mul_of_one_le_left (BasisCost.coeff_nonneg _) (col_ge ..))) (hbase _)

include H hprep hr in
lemma rewind (hG : G.Simple) {A : Bands R (C.path.rep N p m)} {A' : Bands R (C.path.rep N p (m+1))}
    (h : Raw C A A' D t) (hI : A.Active) (hn : ∀ i, C.ref (D i) ≤ m) (hm : m < N)
    (hp : Fresh hot R A.origins (point C m).B) (hμ : Occupancy A.origins (s.markers (year C m)))
    (he : Spent entire A' (rate C (m+1) t hot D r N) 0 (divisor C (m+1)) ((gHat C (m+1))^2/2)) :
    Spent mixed A (rate C m t hot D r N) 0 (divisor C m) ((gHat C m)^4) := by
  have h0 (j v) : 0<rate C j t hot D r N v := rate_pos hot (hr v)
  have hf := h _ (h0 _) he
  let b := quote C m t
  have hb : 1≤ b := quote_ge ..
  have hg := gHat_pos C m
  let P := (C.path.rep N p m).p
  have hv : P = point C m := (H.wilson.represents _ p _ hm.le).vac
  have hB : 8 ≤ P.B := hv.symm ▸ (hprep.here m).large
  have hD : 1 ≤ b / gHat C m^4 := (one_le_div (by positivity)).mpr ((pow_le_one₀ hg.le (gHat_le_one ..)).trans hb)
  have hh v := switch (C:=C) (N:=N) (t:=t) hot hG (D:=D) (admitted C _ H ((hn v).trans (Nat.le_succ _))) (r:=r) (hr v) hm
  convert hf.reset hI hot (s.markers_pos _) hμ hB (fun v => (h0 m v).le) (fun v => (div_pos (h0 (m+1) v) (scaleFee_pos ..)).le)
    hD (jump_ge ..) zero_le_one (fun v hv => (hh v).1 hv) (fun v hv => (hh v).2 hv) (by dsimp only [P] at hv; rw [one_mul,hv]; exact hprep.across m)
    ((hv.symm ▸ hp : Fresh hot R A.origins P.B).packs (by omega)) using 1
  have hb' : 0 < b := by linarith; -- needed for cancellation
  change gHat C m ^4 = b/(b/gHat C m^4); field_simp

/-- Physical data *before* the mixed quantitative induction. -/
structure Skeleton (C : Family G) (L : Lane C.path R N p) (D : V → ℕ) (v : ∀ i,C.label (D i)) (k : ℕ) : Prop where
  load : L.load=D
  fields i : L.uses i=C.O N p (v i) ((L.sites N).origins i)
  active j : k≤j → j≤N → (L.sites j).Active
  copy j : k≤j → j≤N → ∀ i, Copied (L.sites j) i (v i)
  aligned j : k ≤ j → j < N → ∀ i, (C.path.levels.clock.op j p).ratio.parent ((L.sites (j+1)).origins i)=(L.sites j).origins i
  first s U : L.signal N s U = Ride.bump (C.S.a N) s L.load * (Wilson.bare (C.beta N p) U : ℂ)*Ride.Product (H:=C.path) L.uses s U
  transforms j s : k≤j → j<N → L.signal j s=(Ride.bump (↑(C.S.block j).val) s L.load) •
    (C.path.levels.clock.op j p).push (C.path.β N p (j+1)) (L.signal (j+1) s)

structure Unbilled (C : Family G) (L : Lane C.path R N p) (D : V → ℕ) (v : ∀ i,C.label (D i)) (k : ℕ) (t : Tariff)
    : Prop extends Skeleton C L D v k where
  birth : Opening C (L.sites N) D v
  raw j : k ≤ j → j<N → Raw C (L.sites j) (L.sites (j+1)) D t

namespace Unbilled
variable {L : Lane C.path R N p} (h : Unbilled C L D u i t) (hG : G.Simple)
  (hμ : ∀ j, i ≤ j → j ≤ N → Occupancy (L.sites j).origins (s.markers (year C j)))
  (hsep : ∀ j, i ≤ j → j ≤ N → Fresh hot R (L.sites j).origins (point C j).B)
  (hborn : Thick C N p) (hstart : ∀ v,C.ref (D v) ≤ i)

include h
theorem reads (x : R.Mode) : Integrable (Ride.Product (H:=C.path) L.uses x) (law G (C.side N p) (C.beta N p)) := by
  apply continuous_integrable
  unfold Ride.Product; refine continuous_finsetProd _ (fun i _ => ?_)
  rw [h.fields]; exact C.continuousO ..

include hsep hμ hG hstart hborn H hr hc hprep

theorem realizes (hm : i ≤ m) (hn : m ≤ N) :
    let w := rate C m t hot D r N
    (∀ v,w v * ‖(L.sites m).units v‖ ≤ 1) ∧ Spent entire (L.sites m) w 0 (divisor C m) (gHat C m^2/2) := by
  induction hn using Nat.decreasingInduction with
  | self =>
    have hs := fun v => (hstart v).trans hm
    have he i := (hprep.here N).atlas (D i) (admitted C N H (hs i))
    obtain ⟨h1,h2⟩ := copied_price H (h.copy N hm le_rfl) hs le_rfl hr hc (fun i => (rate_pos hot (hr i)).le)
      (fun i => rate_le hot (hr i)) (fun i => (he i).1) (hprep.here N).singletons
    have hB := born_mixed H hprep hot hr hc hborn (h.active N hm le_rfl) hs (hμ N hm le_rfl) h.birth
    refine ⟨h1, (h2.complete (h.active _ hm le_rfl) (fun i => (rate_pos hot (hr i)).le) (divisor_pos ..).le hB).mono
      (fun i => (rate_pos hot (hr i)).le) (fun _ => le_rfl) (divisor_pos ..).le ?_ (fun _ h => h) (fun _ h => h)⟩
    have he : gHat C N ≤ 1/4 := (hprep.here N).perturb
    have ht := gHat_pos C N
    nlinarith [mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ht.le he 2) (sq_nonneg (gHat C N))]
  | of_succ m hn ih =>
    have hs := fun v => (hstart v).trans hm
    have he i := (hprep.here m).atlas (D i) (admitted C m H (hs i))
    obtain ⟨h1,h2⟩ := copied_price H (h.copy m hm hn.le) hs hn.le hr hc (fun i => (rate_pos hot (hr i)).le)
      (fun i => rate_le hot (hr i)) (fun i => (he i).1) (hprep.here m).singletons
    have hM := rewind H hprep hot hr hG (h.raw m hm hn) (h.active m hm hn.le) hs hn (hsep m hm hn.le) (hμ m hm hn.le)
      (ih (hm.trans (Nat.le_succ m))).2
    refine ⟨h1, (h2.complete (h.active _ hm hn.le) (fun i => (rate_pos hot (hr i)).le) (divisor_pos ..).le hM).mono
      (fun i => (rate_pos hot (hr i)).le) (fun _ => le_rfl) (divisor_pos ..).le ?_ (fun _ h => h) (fun _ h => h)⟩
    have he : gHat C m ≤ 1/4 := (hprep.here m).perturb
    have ht := gHat_pos C m
    nlinarith [mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ht.le he 2) (sq_nonneg (gHat C m))]

theorem radial (hm : i ≤ m) (hn : m ≤ N) : (L.sites m).Radial (rate C m t hot D r N) 1 1 1 (divisor C m) := by
  obtain ⟨hx,hh⟩ := h.realizes H hprep hot hr hc hG hμ hsep hborn hstart hm hn
  have he : gHat C m ^2 / 2 ≤ 1 := by have := gHat_le_one C m; have := gHat_pos C m; nlinarith
  exact (hh.mono (fun i => (rate_pos hot (hr i)).le) (fun _ => le_rfl) (divisor_pos ..).le he
    (ok':=entire) (fun _ h => h) (fun _ h => h)).radial (fun i => rate_pos hot (hr i)) (divisor_pos ..) hx

include hot in
theorem usable (hn : i ≤ N) : L.Works i := by
  refine ⟨hn,fun j hj hk => ⟨h.active j hj hk,_,_,_,_,_,h.radial H hprep hot hr hc hG hμ hsep hborn hstart hj hk⟩,
    fun j v h1 h2 => h.aligned j h1 h2 v,h.reads,h.first,fun j h1 h2 x => h.transforms j x h1 h2⟩
end Unbilled

end YM.Extra.Multi
