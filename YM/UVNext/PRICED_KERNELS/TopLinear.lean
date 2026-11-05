import YM.UVNext.PRICED_KERNELS.Echo
import YM.UVNext.PRICED_KERNELS.Order



set_option warningAsError false


set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

/-!
# Variant of the priced linear producer targeted at E top matching

Using **exactly the same `Next.Free` formulae**, choose two pre-L l
parameters per smoothing index: the top input metric (at the exact top only)
may take l=0, other amended metrics still take large l from Flight.buys
( takes the latter also at the top). Only the latter
can be the *output* of an actual RG step. No dependence on delays or L.
This variant enables a local path top correction with Wilson normalization
without having to covariantize the  formula and telescope on path
errors. It also means the top itself doesn't meet the absolute-stationary
pre-L quote `Present.a` from `shelves` with a single table l.(J). Instead
we obtain all the SAME Floor, Rack etc contracts on both Horizons with a
separate provenance `Vertical`; also continue to offer the ordinary Wired
linear producer through `wire` on these same Before numbers. DO NOT take
some results for the latter and apply to this variant Horizon: if attempting
to use BOTH must choose the same across Consumers; suggestions: use
`Rewired.toMotor`, get all general Motor results, use the ordinary producer
only as an alternative, not a collaborator. The core freezing API unchanged
and all quotes including for top chosen before L.

No change nor assumption on nonabelian normalization/rank; K is in
KernelChoices incl positive penalty, and free input isn't a baby kernel
or degenerate zero-coupling example. In particular l=0 does not set
penalty or path mass/Loop caps to zero. Diagonal, potential precision,
A0/T unchanged at all levels. Full H data on Levels includes metric/roots
which WILL differ from the ordinary wired example at least in their
provenance. Use raw and V on this choice alone, preserving those data.
-/
set_option autoImplicit false
noncomputable section
namespace YM.UVNext.PricedKernels
open Filter Function Lattice RG RG.Supply Wilson Precision Craft Pressure Laurent Exterior Bloch
open Push.PriceCompiler Next.Free Work.F08
open scoped Topology Matrix.Norms.Frobenius BigOperators
variable {G : Gauge}

/-- Delta top metric factor. Offered for any canonical path usage, with winding
evaluations allowed; accepting this offer can place the coefficient at route
`[]`. Not forced to symmetrize shortest paths across whole ensemble here.
-/
def delta (p : Clip) : Row (TypeFace 2) (TypeFace 2) := scaleRows (Real.sqrt (1-p.direct)) (unitRow _)

lemma delta_square (p : Clip) (u : p.direct ≤ 1) (n : Side) :
    p.direct • (1: Matrix (Body 2 n) _ ℝ) + ((delta p).acts n).transpose * (delta p).acts n = 1 := by
  simp only [delta,acts_scale,acts_unit,Matrix.transpose_smul,Matrix.transpose_one,Matrix.smul_mul,
    Matrix.one_mul,smul_smul,Real.mul_self_sqrt (sub_nonneg_of_le u), ← add_smul]
  rw [add_sub_cancel,one_smul]

lemma delta_strip (p : Clip) (u : p.direct ≤ 1) (s : ℝ) : (delta p).strip s 1 := by
  have hz : 0 ≤ 1-p.direct := sub_nonneg_of_le u
  apply Work.F08.strip_mono (strip_scale strip_unit (Real.sqrt (1-p.direct))) le_rfl
  rw [Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
  nlinarith [p.quadratic_pos,Real.sq_sqrt hz]

/-- Request from pledges-like code at each admitted index. -/
def CepQuote (K : KernelChoices) (j : ℕ) (γ σ η A : ℝ) :=
    ∀ (p : Clip), p.direct ≤ γ → ∃ M : Bed, Defined K.penalty 0 (Train.top j) M ∧
        M.diagonal.acts = (fun n => (1:Matrix (Body 2 n) _ ℝ)) ∧ M.metric.acts = (fun n => (1:Matrix (Body 2 n) _ ℝ))
        ∧ M.roots = delta p ∧ M.covered σ A ∧ (∀ n, Floor M p n η A) ∧ (∀ n G, Bid.Sworn M n G)
lemma priced_tip (K : KernelChoices) (j : ℕ) (hj : 4 ≤ j) :
    ∃ γ σ η A : ℝ, 0<γ ∧ 0<σ ∧ 0<η ∧ CepQuote K j γ σ η A := by
  obtain ⟨γ,s,η,A,hγ,hs,hη,hA,h⟩ := bid_bed K.penalty 0 K.penalty_pos (le_refl _) hj
  refine ⟨min 1 γ,s,η,max 1 A,lt_min one_pos hγ,hs,hη,?_⟩
  intro p he
  have hu := he.trans (min_le_left ..); have hg := he.trans (min_le_right ..)
  let v := Train.top j; let k := K.penalty
  obtain ⟨M,hM,hC,hF,hB,hT⟩ := h p hg v
  let V := { M with roots:=delta p }
  have hdiag : ∀ n, M.diagonal.acts n=1 := hT rfl
  have hmetric : ∀ n, M.metric.acts n=1 := by
    intro n
    -- Cf. BHtil, repair on inverse identity component trivial
    obtain ⟨h₁,h₂,-⟩ := obligations k 0 K.penalty_pos (le_refl _) hj v n
    suffices ht : (blue k v).acts n=1 by
      have H := h₂.2
      rw [ht,zero_smul,add_zero] at H
      have hp := h₂.1
      rw [H,Matrix.mul_one] at hp; rw [hM.metric]; exact hp
    rw [← hM.diag,hdiag,Matrix.one_mul] at h₁; exact h₁
  have hv : Defined k 0 v V := ⟨hM.diag,hM.dual,hM.metric,hM.inverse⟩
  refine ⟨V,hv,funext hdiag,funext hmetric,rfl,?_,?_,?hB⟩
  · obtain ⟨ha,hk,hI,_,hf⟩ := Next.Free.cover_revise hC le_rfl (le_max_right 1 A)
    exact ⟨ha,hk,hI,Work.F08.strip_mono (delta_strip p hu _) le_rfl (le_max_left ..),hf⟩
  · intro n
    let H := Next.Free.floor_revise (hF n) le_rfl (le_max_right 1 A)
    refine { H with roots := ?_ }
    rw [full_cover,show V.metric=M.metric from rfl,hmetric]; exact delta_square p hu _
  intro n G; exact hB n G

structure Consecutive (K : KernelChoices) (q : MapPrices) (l γ : ℕ → ℝ) (b : ℕ → ℕ) : Prop extends Catalog K q l γ b where
  special j : 4 ≤ j → CepQuote K j (γ j) (q.α j) (q.η j) (q.Ω j)
  hops j i : Mag j i → HopQuote K j i 0 (l i) (q.α j) (q.η j) (q.Ω j) (b j)

lemma CepQuote.revise {j K γ σ v A γ' s u a} (h : CepQuote K j γ σ v A)
    (hγ : γ' ≤ γ) (hs : s ≤ σ) (hv : u ≤ v) (hA : A ≤ a) : CepQuote K j γ' s u a := by
  intro p hp
  obtain ⟨V,hD,h₁,h₂,hr,hC,hF,hB⟩ := h p (hp.trans hγ)
  exact ⟨V,hD,h₁,h₂,hr,cover_revise hC hs hA,fun n => floor_revise (hF n) hv hA,hB⟩

/-- Combined pre-L purchase. Quantifiers just like those used in `pledges`,
but includes edges when i+1 is the top and l_{i+1}=0 despite J(i)=J(i+1).
The earlier producer may also buy at these very same tables. This doesn't
preclude the extra b floors & other asks on P later. -/
lemma preps (K : KernelChoices) : ∃ q l γ b, Consecutive K q l γ b := by
  classical
  choose δ hδ h using Next.Free.buys K
  let l (i : ℕ) := max (δ i i) (δ (i+1) i)
  have hl i : 0 ≤ l i := (hδ i i).le.trans (le_max_left ..)
  have he (j i : ℕ) : ∃ s u A : ℝ, ∃ n : ℕ, 0 < s ∧ 0 < u ∧
      (Mag j i → HopQuote K j i (l j) (l i) s u A n ∧ HopQuote K j i 0 (l i) s u A n) := by
    by_cases hg : Mag j i
    · have hu : δ j i ≤ l i := by
        rcases hg.2.2 with hh|hh
        · rw [← hh]; exact le_max_left ..
        rw [← hh]; exact le_max_right ..
      obtain ⟨c,v,V,b,hc,hv,hV⟩ := h j i (l j) (l i) (hl j) hu
      obtain ⟨d,w,W,a,hd,hw,hW⟩ := h j i 0 (l i) le_rfl hu
      exact ⟨min c d, min v w, max V W, max b a, lt_min hc hd, lt_min hv hw, fun _ =>
        ⟨(hV hg).revise (min_le_left ..) (min_le_left ..) (le_max_left ..) (le_max_left ..),
          (hW hg).revise (min_le_right ..) (min_le_right ..) (le_max_right ..) (le_max_right ..)⟩⟩
    exact ⟨1,1,1,1,one_pos,one_pos,fun hf => False.elim (hg hf)⟩
  choose s u A n hs hu hJ using he
  have hb (j : ℕ) : ∃ γ σ v C : ℝ, 0<γ ∧ 0<σ ∧ 0<v ∧
      (4 ≤ j → BottomQuote K j (l j) γ σ v C ∧ CepQuote K j γ σ v C) := by
    by_cases hg : 4 ≤ j
    · obtain ⟨γ,σ,v,C,hγ,hσ,hv,-,hh⟩ := bid_bed K.penalty (l j) K.penalty_pos (hl _) hg
      obtain ⟨a,t,w,D,ha,ht,hw,hf⟩ := priced_tip K j hg
      have hx : BottomQuote K j (l j) γ σ v C := hh
      exact ⟨min γ a,min σ t,min v w,max C D,lt_min hγ ha,lt_min hσ ht,lt_min hv hw,fun _ =>
        ⟨fun p hi R => hx.revise (min_le_left ..) (min_le_left ..) (le_max_left ..) p (hi.trans (min_le_left ..)) R,
          hf.revise (min_le_right ..) (min_le_right ..) (min_le_right ..) (le_max_right ..)⟩⟩
    exact ⟨1,1,1,1,one_pos,one_pos,one_pos,fun hf => False.elim (hg hf)⟩
  choose γ t v C hγ ht hv hK using hb
  let Q : MapPrices := ⟨fun i => min (t i) (min (s i i) (s i (i-1))), fun i => max (C i) (max (A i i) (A i (i-1))),
    fun i => min (v i) (min (u i i) (u i (i-1))),fun i => lt_min (ht i) (lt_min (hs i i) (hs i (i-1))),
    fun i => lt_min (hv i) (lt_min (hu i i) (hu i (i-1)))⟩
  let b i := max (n i i) (n i (i-1))
  have hp (i j : ℕ) (he : Mag i j) : Q.α i ≤ s i j ∧ A i j ≤ Q.Ω i ∧ Q.η i ≤ u i j ∧ n i j ≤ b i := by
    rcases (show j=i ∨ j=i-1 by obtain hx := he.2.2; omega) with hh|hh
    · rw [hh]
      exact ⟨(min_le_right ..).trans (min_le_left ..),(le_max_left ..).trans (le_max_right ..), (min_le_right ..).trans (min_le_left ..),le_max_left ..⟩
    rw [hh]
    exact ⟨(min_le_right ..).trans (min_le_right ..),(le_max_right ..).trans (le_max_right ..), (min_le_right ..).trans (min_le_right ..),le_max_right ..⟩
  refine ⟨Q,l,γ,b,⟨hl,hγ,fun j hh => ?_,fun j i hh => ?_⟩,fun j hh => ?_,fun j i hh => ?_⟩
  · exact (hK j hh).1.revise (min_le_left ..) (min_le_left ..) (le_max_left ..)
  · obtain ⟨ha,hΩ,hη,hb⟩ := hp j i hh; exact (hJ j i hh).1.revise ha hη hΩ hb
  · exact (hK j hh).2.revise le_rfl (min_le_left ..) (min_le_left ..) (le_max_left ..)
  obtain ⟨ha,hΩ,hη,hb⟩ := hp j i hh; exact (hJ j i hh).2.revise ha hη hΩ hb

/-- Occurrence-indexed l prices. -/
def tips (a : Levels G) (N i : ℕ) (l : ℕ → ℝ) : ℝ := if N=i then 0 else l (a.clock.J i)

structure Vertical (a : Levels G) (B : Horizon a) (l : ℕ → ℝ) : Prop where
  defined (N i : ℕ) : i ≤ N → Defined a.clock.kernel.penalty (tips a N i l) (location a N i) (B.H N i)
  hop (N i : ℕ) : i < N → (B.towers N i).A0=((destination a N i).duo a.clock.kernel.penalty).A0 ∧
    (B.towers N i).T=((destination a N i).duo a.clock.kernel.penalty).T
  base (N : ℕ) : (B.H N N).roots = delta (a.params N).clip ∧ ∀ n,(B.H N N).metric.acts n=1

/-- Same linear Pillar incl arbitrary periods. -/
lemma toolkit {a : Levels G} {q l γ b} (hv : Consecutive a.clock.kernel q l γ b) (he : Credit a γ b) :
    ∃ B : Horizon a, Rack a q B ∧ Vertical a B l := by
  choose Y hY hc hf hb ht using fun N i => hv.bottom (a.clock.J i) (a.clock.adm _) (a.params i).clip (he.1 _) (location a N i)
  choose V hV h₁ h₂ hr hC hF hB using fun i => hv.special (a.clock.J i) (a.clock.adm i) _ (he.1 i)
  let k := a.clock.kernel
  let B : Horizon a := ⟨fun N i => if N=i then V i else Y N i,fun N i => (destination a N i).duo k.penalty⟩
  have hn i (N : ℕ) (h : i < N) : B.H N i=Y N i := if_neg (by omega)
  have hh i : B.H i i=V i := if_pos rfl
  have hh' : Vertical a B l := by
    refine ⟨fun N i h => ?_,fun _ _ _ => ⟨rfl,rfl⟩,fun N => ?_⟩
    · rcases Nat.lt_or_eq_of_le h with h|rfl
      · rw [tips,if_neg (show ¬ N=i by omega),hn i N h]; exact hY N i
      rw [hh,loc_top,tips,if_pos rfl]; exact hV _
    rw [hh]; exact ⟨hr N,fun n => congrFun (h₂ N) _⟩
  have hM i : Mag (a.clock.J (i+1)) (a.clock.J i) := by
    let P := destination a 0 i; have ht := P.narrow; have hh := P.mono
    exact ⟨a.clock.adm _,a.clock.adm _,by omega⟩
  have hJ (N i : ℕ) (h : i < N) : HopQuote k (a.clock.J (i+1)) (a.clock.J i) (tips a N (i+1) l) (tips a N i l)
      (q.α (a.clock.J (i+1))) (q.η (a.clock.J (i+1))) (q.Ω (a.clock.J (i+1))) (b (a.clock.J (i+1))) := by
    unfold tips; rw [if_neg (show ¬ N=i by omega)]
    split_ifs
    · exact hv.hops _ _ (hM i)
    exact hv.hop _ _ (hM i)
  have hpos (N i : ℕ) : 0 ≤ tips a N i l := by unfold tips; split_ifs; rfl; exact hv.net _
  refine ⟨B,⟨?_,?_,?_,?_,?_,?_,?_⟩,hh'⟩
  · intro N i h
    rcases Nat.lt_or_eq_of_le h with h|rfl
    · rw [hn i N h]; exact hc N i
    rw [hh]; exact hC _
  · intro N i h n
    rcases Nat.lt_or_eq_of_le h with h|rfl
    · rw [hn i N h]; exact hf N i n
    rw [hh]; exact hF _ _
  · intro N i n h
    rcases Nat.lt_or_eq_of_le h with h|rfl
    · rw [hn i N h]; exact hb N i _ _
    rw [hh]; exact hB _ _ _
  · intro N n; rw [hh]; exact congrFun (h₁ N) n
  · intro N i h; exact (hJ N i h (destination a N i)).1
  · intro N i p h
    exact Next.Free.diagonal k (tips a N i l) (tips a N (i+1) l) (hpos ..) (hpos ..) (destination a N i)
      (a.clock.adm i) (B.H N (i+1)) (B.H N i) (hh'.defined N (i+1) h) (loc_land a N i h ▸ hh'.defined N i h.le)
      (c:=a.S.side i p) (f:=a.S.side (i+1) p) (a.S.oneStep i p).exact_size
  intro N i h; obtain ⟨_,hy,hf⟩ := hJ N i h (destination a N i)
  exact ⟨(destination a N i).rollFunds k.penalty (tips a N (i+1) l) (tips a N i l),hy,fun p hp => ⟨(hf (he.2 i) p hp).1,fun x => ((hf (he.2 i) p hp).2 _).1⟩,
    fun p => check_bleep k (tips a N i l) (tips a N (i+1) l) (hpos ..) (hpos ..) (destination a N i)
      (a.clock.adm i) (B.H N (i+1)) (B.H N i) (hh'.defined N (i+1) h) (loc_land a N i h ▸ hh'.defined N i h.le)
      (c:=a.S.side i p) (f:=a.S.side (i+1) p) (a.S.oneStep i p).exact_size⟩


/-- Don't conflate with Wired. SAME engine all periods, plus enables a possibly
much more local startup strategy (which doesn't need any new kernel assumptions).
Top reads revised l, every lower occurrence reads same l; even the Next.Free
formula for defect lifts and all-period estimates still work. Keep p.frozen G
for ALL later spends. -/
structure Rewired (P : Before) (a : Levels G) (X : MapPrices) (l : ℕ → ℝ) (B V : Horizon a) : Prop extends Motor P a V where
  numbers : P.flat.Estimates a B
  raw : Rack a X B
  derived : Vertical a B l
  sameTrain : Vertical a V l
  stayed : Bid.Retained V B

variable {P : Before} {f : ℕ → ℕ} {D : Rolls (P.sheet G f)}
  {M : Preparations P D} {T : Protection D} {W : Delays T} {Y : Bar W} {I : Wait Y}
  {a : Levels G}

/-- Permit outs with the either variant. ALWAYS keep own Beds across consumers:
provenance through `Retained`. -/
theorem rewire (p : Permit M I a) {K : KernelChoices} {X : MapPrices} {l γ b}
    (hX : Consecutive K X l γ b) (hk : P.kernelChoice G = K)
    (hF : P.flat = flatOf X)
    (hC : ∀ i, P.first ≤ i → (P.clip i).direct ≤ γ i)
    (hL : ∀ i, P.first ≤ i → b i ≤ f i) :
    ∃ B V : Horizon a, Rewired P a X l B V := by
  have he : Next.Free.Credit a γ b := Next.Free.credit_from_sheet p.paid γ b hC hL
  obtain ⟨B,hR,hP⟩ := toolkit ((p.paid.kernel.trans hk).symm ▸ hX) he
  have ht : P.flat.Estimates a B := hF.symm ▸ estimates_of_rack hR
  obtain ⟨V,hV,hS⟩ := p.kernel ht
  refine ⟨B,V,⟨hS,fun N m n hm => hV.1.symm ▸ hR.oath N m n hm⟩,ht,hR,hP,⟨?_,?_,?_⟩,hV⟩
  · intro N i hi; rw [hV.1]; exact hP.defined N i hi
  · intro N i hi
    exact ⟨((hV.2 N i hi).1.trans ((hP.hop N i hi).1)),((hV.2 N i hi).2.trans ((hP.hop N i hi).2))⟩
  intro N; rw [hV.1]; exact hP.base N







/-- Schedule and Permit consumer supporting BOTH variants. Choose according
to application: ordinary (`Free.Present`) variant producing Wired, or tipped
l variant producing Rewired. Nonlinear estimates according to own version; all
pre-L issuances can include e.g. LayoutPrices or kernel or volume contour wants
as long as honoring this DAG and providing the corresponding actual Charges
proofs based only on pre-L data. -/
theorem both_compilers (hG : G.Simple) (p : Before) :
    ∃ X l γ b, Consecutive (p.kernelChoice G) X l γ b ∧
      ∀ (c : Caps p.first γ) (R : Charges), let P := issue G p (flatOf X) c.clips R
        Canonical.Quotes (P.frozen G) P.opening P.amount ∧
          ∀ e : ℕ → ℕ, ∃ f : ℕ → ℕ, Monotone f ∧ e ≤ f ∧ b ≤ f ∧ ∀ g : ℕ → ℕ, f ≤ g →
            Built G P X l g ∧ ∀ (D : Rolls (P.sheet G g)) (M : Preparations P D)
              (T : Protection D) (W : Delays T) (Y : Bar W) (I : Wait Y) (a : Levels G), Permit M I a →
              ∃ B V : Horizon a, Rewired P a X l B V := by
  obtain ⟨X,l,γ,b,h⟩ := preps (p.kernelChoice G)
  refine ⟨X,l,γ,b,h,fun c R => ?_⟩
  intro P
  refine ⟨(linear_paths G p (flatOf X) c.clips R).1,fun e => ?_⟩
  obtain ⟨f,hf,he,H⟩ := compile_prices hG P (fun i => max (e i) (b i))
  have hb : b ≤ f := fun i => le_trans (le_max_right ..) (he i)
  refine ⟨f,hf,fun i => le_trans (le_max_left ..) (he i), hb, fun g hg => ?_⟩
  obtain ⟨hh,hr,hM⟩ := H g hg
  refine ⟨⟨hh,hr,hM,?_⟩,?_⟩ <;> intro D M T W Y I a ha
  · exact wire ha h.toCatalog rfl rfl c.meets (fun i _ => (hb i).trans (hg i))
  exact rewire ha h rfl rfl c.meets (fun i _ => (hb i).trans (hg i))

end YM.UVNext.PricedKernels
