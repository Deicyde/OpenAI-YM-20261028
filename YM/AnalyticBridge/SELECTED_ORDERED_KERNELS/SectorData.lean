import YM.AnalyticBridge.SELECTED_ORDERED_KERNELS.SectorSmooth
import YM.Next.SCHEDULE.Final
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Chosen

/-!
# Supply everything except the higher-order forward prices on the actual
# Gaussian.SectorChange selection. Gap for C NOT inferred just from A>0!

Uses opaqueCost, windows, earned and the proven Gram germ argument. These
are real, active-coordinate physical counting matrices incl boundary rows.
Same all-endpoint convention and mask/shots/flags as in SectorChange
(define once and hold them fixed throughout varying the link input).
Remaining input Higher: the position-price precursor on the selected FORWARD
precision's true chart jets at UNscaled unit directions (only positive orders,
and at that V only). Its production (see now AuthorizedLoans at one
scope) is not just a conclusion of the flat affine methods. In particular DO NOT use the
same A|path-cut by pretending selected stencils or Q channels equal the
no-hole uncut ones on a field chart. See report for scope.
-/

set_option autoImplicit false
noncomputable section
namespace YM.SelectedOrderedKernels.Sector
open Lattice Wilson RG Function Filter WardBin.Lies Precision Tree Next.SectorChange
  Next.SectorChange.Motion Next.Fluctuations YM.Pressure YM.Pressure.Stores
  Rows Schur Wisps Tier FreeResolvent Affine Mark TestD Window
open scoped BigOperators Topology Matrix.Norms.Frobenius ContDiff Classical
variable {G : Gauge} {c f m : Side} {S : StepData c f} {x : ℝ}

section survey
variable {ι : Type} [Fintype ι] [DecidableEq ι] {p : ι → Site c} {r : ℕ} {W : ι → Set ι} {s M η : ℝ}

def survey (h : Bars W p r) : Survey (fun i => W i) where
  loc i := ⟨((↑) : W i → ι), Subtype.val_injective⟩
  root i := ⟨i, per_self h i⟩
  atRoot _ := rfl

lemma near_survey (h : Bars W p r) : (survey h).Near (native c) p r := by
  intro i j hj; change (r:ℝ) ≤ separation (p i) (p j)
  exact_mod_cast (lt_of_not_ge (show ¬ separation (p i) (p j) ≤ r from fun hc => hj ⟨⟨j,h i j hc⟩,rfl⟩)).le

lemma inspect_per (h : Bars W p r) (F : Matrix ι ι ℝ) : (survey h).inspect F 0 = Schur.per W F := by
  ext i j
  change Pane.column F ((survey h).loc j) 0 ((survey h).root j) i = _
  by_cases he : i ∈ W j
  · rw [per_read W F (per_self h _) he]
    have hx := Pane.local_entry F 0 (((survey h).loc j) : W j → ι) Subtype.val_injective ((survey h).root j) ⟨i,he⟩
    rw [Pane.thin,resolve,zero_smul,add_zero] at hx; exact hx
  exact (Pane.unused F 0 _ _ _ (fun ⟨t,ht⟩ => he (ht ▸ t.property))).trans (per_zero W F he).symm

lemma inspect_arbitrary [inst : ∀ i, Fintype (W i)] [ie : ∀ i, DecidableEq (W i)] (h : Bars W p r) (F : Matrix ι ι ℝ) :
    (survey h).inspect F 0 = Schur.per W F := by
  let v : ∀ i : ι, Fintype (W i) := fun i => @Subtype.fintype ι _ (fun a => Classical.propDecidable (a ∈ W i)) _
  let u : ∀ i : ι, DecidableEq (W i) := fun i => @Subtype.instDecidableEq _ _ _
  rw [Subsingleton.elim inst v,Subsingleton.elim ie u]; exact inspect_per h F

omit [DecidableEq ι] in
lemma got_schur {F : Matrix ι ι ℝ} (h : Pours F p p s M) : (native c).Schur p p s M F := ⟨⟨h.row⟩,⟨h.turn.row⟩⟩
omit [DecidableEq ι] in
lemma got_gap {F : Matrix ι ι ℝ} (h : Gapped F η) : FreeResolvent.Gap F η := ⟨fun w => (sumSq_dot w) ▸ h w⟩
end survey

def key (G : Gauge) (P : Patch) (σ : ℝ) := ((Fintype.card G.ColorIndex:ℝ) *
    (Fintype.card (Site P.L) * Fintype.card Axis)) * wealth σ
lemma key_nn (G : Gauge) (P : Patch) (σ : ℝ) : 0 ≤ key G P σ := by unfold key; have := wealth_nn σ; positivity
lemma keys (A : Stores S) (T : Forest S.ratio) (G : Gauge) {σ : ℝ} (hσ : 0 < σ) :
    (native c).Volume (front (G:=G) (x:=x) A T) σ (key G S.patch σ) := ⟨front_price σ hσ A T G⟩

def form (H : Tube G S) (x : ℝ) (A : Stores S) (T : Forest S.ratio) (k : S.Choices) (V : Config G c) :=
  Rows.gram H x V k (shots S x) A T

def covariance (H : Tube G S) (x : ℝ) (A : Stores S) (T : Forest S.ratio) (k : S.Choices) (V : Config G c) :=
  fog A T H x V k

variable {V : Config G c} {A : Stores S} {T : Forest S.ratio} {k : S.Choices} {H : Tube G S} {σ t M N r g : ℝ}

structure Ground (H : Tube G S) (x : ℝ) (A : Stores S) (T : Forest S.ratio) (k : S.Choices) (V : Config G c)
    (s M r g : ℝ) : Prop where
  ready : 120 ≤ radiusB x
  gap : FreeResolvent.Gap (form H x A T k V) r
  cloud_gap : FreeResolvent.Gap (covariance H x A T k V) g
  price : (native c).Schur (front A T) (front A T) s M (form H x A T k V)
  germ (j : ℕ) : Germ j (form H x A T k) V

lemma form_sym : Matrix.IsSymm (form H x A T k V) := by
  unfold form Rows.gram Matrix.IsSymm; rw [Matrix.transpose_mul,Matrix.transpose_transpose]

theorem ground_supply (G : Gauge) (P : Patch) (Pt : Teller G) (hp : P.Branches Pt.bind G) :
    ∃ s M r g : ℝ, 0 < s ∧ 0 ≤ M ∧ 0 < r ∧ 0 < g ∧ ∀ᶠ x : ℝ in atTop,
    ∀ {c f : Side} (S : StepData c f) (H : Tube G S),
    S.patch=P → 100*(1+radiusB x) ≤ c.val → Pt.Funds S H →
    ∀ (A : Stores S) (F : Forest S.ratio) (k:S.Choices) (V : Config G c), A.flags=RG.flags (temp x) V → Ground H x A F k V s M r g := by
  obtain ⟨s,M,r,b,y,hs,hM,hr,-,-,H⟩ := opaqueCost G P Pt hp
  obtain ⟨b',y',g,-,-,hg,h⟩ := Schur.windows hs hr hM _ (key_nn G P)
  obtain ⟨C,δ,-,hδ,hQ⟩ := earned P Pt.bind G hp
  have ht : ∀ᶠ x : ℝ in atTop, LocalJet.permit P * temp x ≤ δ := by
    have h0 := Work.E01.fiery_le G (1:Side) (LocalJet.permit P)
    filter_upwards [h0, (Work.E01.largeT_tendsto G 1).eventually (ge_mem_nhds hδ)] with x hx he
    simpa [fiery,betaF] using hx.trans he
  have hB : Tendsto (fun x => radiusB x / 60) atTop atTop := by
    apply Filter.tendsto_atTop.mpr; intro i
    filter_upwards [Work.E01.radiusB_tendsto.eventually_ge_atTop (60*i)] with x hx; omega
  refine ⟨s,M,r,g,hs,hM,hr,hg,?_⟩
  filter_upwards [H,hB.eventually h,ht, small_span P, Work.E01.radiusB_tendsto.eventually_ge_atTop (LocalJet.allot P+120)] with x hx hw ht hS hb
  intro c f S T hP hR hT A F k V hV
  obtain ⟨hm,he,-⟩ := hx S T hP hR hT A F k V hV
  have hi : Revenue (front A F (G:=G) (x:=x)) (key G P) := fun y hy i => hP ▸ front_price y hy A F G i
  have h0 : 120 ≤ radiusB x := by omega
  have hh := hw (front A F) (form T x A F k V) (panels A F) hi hm form_sym he (boards A F G h0)
  exact ⟨h0,got_gap he,got_gap hh.2.1,got_schur hm,fun j => gram_smooth T hT (hQ S hP hT.knobs F A V x hV hS (by omega) (by omega) ht) k⟩

/-- Remaining quantitative derivative income; true placement of each raw
chart coordinate perturbation. More precise than polynomial-growth tests
on normalized directions; sector jets work may vary the widths by order
before furnishing common minimum σ and max price. This alone cannot turn
a flagged precision with a kernel/nullspace into a usable one. -/
structure Higher (H : Tube G S) (x : ℝ) (A : Stores S) (T : Forest S.ratio) (k : S.Choices) (V : Config G c)
    (j : ℕ) (σ N : ℝ) : Prop where
  jets (l : List (raw G c)) : l ≠ [] → l.length ≤ j → Bill (marks G c σ) (native c) (front A T) (front A T) l σ N
    (jet (ray G c) (over (form H x A T k) V) l 0)

lemma plan {q : ℕ} {s M r : ℝ} (hs : 0 < s) (hm : 0 ≤ M) (hr : 0 < r) (P : Patch) (G : Gauge) :
    let d := room s M r q
    Price s M r d 1 (key G P d) 1 q := ⟨hr,hm,hs,rfl,le_rfl,key_nn ..,zero_le_one,le_rfl⟩

lemma room_le {q : ℕ} {d r s M ε U Y : ℝ} (hx : Price s M r d U Y ε q) : d ≤ s := by
  apply le_trans ?_ (hx.roomEnough.trans hx.roomTop)
  have := hx.pos; push_cast; nlinarith [show 0 ≤ (q:ℝ)*d by positivity]

theorem input {j : ℕ} (hs : 0 < σ) (ht : 0 < t) (hm : 0 ≤ M) (hr : 0 < r)
    (h : Ground H x A T k V t M r g) (hF : Higher H x A T k V j σ N) :
    let s := min σ t; let K := max M N; let d := TestD.room s K r j
    Data (native c) (front A T) Prod.fst j s K r d 1 (form H x A T k) V := by
  intro s K d; have hK := hm.trans (le_max_left M N)
  have hp := plan (q:=j) (lt_min hs ht) hK hr S.patch G
  have hz : over (form H x A T k) V 0=form H x A T k V := by rw [over,map_zero,Motion.increment_zero]
  refine ⟨smooth_over.mpr (h.germ j),hz.symm ▸ h.gap,hz.symm ▸ (h.price.mono (min_le_right ..) (le_max_left ..)),fun l hL hl => ?_⟩
  rw [mul_one]
  have hb := (hF.jets l hL hl).mono (min_le_left σ t) (le_max_right M N)
  nth_rw 1 [← List.ofFn_get l] at hb ⊢
  have hd : d ≤ σ := (room_le hp).trans (min_le_left ..)
  exact ⟨discount (a:=Prod.fst) (z:=l.get) hb.row hd,discount (a:=Prod.fst) (z:=l.get) hb.col hd⟩
end YM.SelectedOrderedKernels.Sector
