import YM.Next.UV_STRESS.Union
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Discs
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Layering
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Swatches
import YM.Push.PRICE_COMPILER.Powers

/-!
# Construct K, cost of incidence and scalar density recurrence

Exercises actual unmarked continuation port. E exponent match
(on good/bad sectors, in the same library) still has to be supplied;
can't conclude from Candle status. `clear_stencil`: in the no-hole
situation with flags globally empty one gets a real relation to
push already without this. `perceived`: from the full list,
assemble actual updated Rep evaluation on Q = push of R.eval.
Needs Coupler etc. on these precise choices.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Display.Sew
open Lattice Wilson Pressure RG MeasureTheory Function Next.SectorChange Matrix Finset
     Tree Push.SectorMeasure Next.Rank Tapes Value Marker Ac Glyph Thirst Docking
     Flux Bid SectorNext.Vacuum Precision Baler
open scoped Topology BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {x τ : ℝ} {L : Lantern G S} {T : Tube G S}
    {P : Teller G} {W ι κ α β : Type} [Fintype W] [DecidableEq W]
    [Fintype ι] [Fintype α]
section extra
variable {u : W →Site c} {b : BudgetPoint} {s t m : ℝ} (v : W→ℝ)
lemma billed_again {Z : ι→Lifted G u b.threshold} (H : Stripes b Z v t m) (hs : s≤t) (hv : ∀ i,0 < v i) : Stripes b Z v s m:= by
  obtain ⟨q,h,H⟩:=H; refine ⟨q,fun i=>⟨(h _).1,fun U=>?_⟩,H⟩
  refine le_trans ?_ ((h i).2 U); unfold charge; gcongr; exact (Poly.worth hv _).le
-- unmarked incidence: read backward at same cost.
lemma pull_stripe {Z : ι→Lifted G u b.threshold} {Y : α→Lifted G u b.threshold} (E : Embedded Z (Plug.raid∘Y)) (h : Stripes b Y v t m) : Stripes b Z v t m:= by
  obtain ⟨c,H,h⟩:=h
  have hp (i) : Z i=Y (E.wire i):= (Plug.raid.inj (E.found i)).symm
  refine ⟨fun i=>c (E.wire i),fun i=> (hp i).symm ▸ H (E.wire i),fun i=> ?_⟩
  apply le_trans _ (h i)
  let f j:=if i∈(Y j).extent then c j else 0
  have hh j:0≤f j:=by unfold f;split;exact (H j).1;exact le_rfl
  have hx:(∑ j:ι,f (E.wire j))≤∑ j,f j:= by
    rw [← Finset.sum_map (f:=f) univ E.wire]; exact Finset.sum_le_sum_of_subset_of_nonneg (subset_univ _) fun i _ _=>hh _
  exact (le_of_eq (Finset.sum_congr rfl (show ∀ j∈ Finset.univ,(if i∈(Z j).extent then c (E.wire j) else 0) = f (E.wire j) from fun j _=>by rw [hp]))).trans hx -- proof inst
end extra
section closure
variable (R : Rep G f) (R' : Rep G c) (p : ι→ Zest G S x L.park R'.p.threshold) (A : Boosted T P x) (hs : 25*radiusB x+30 ≤ R'.p.B)
    {o ℓ δ Λ η M l σ e y w v : ℝ} (hR : R.Lawful o ℓ Λ δ η)
    {ν : Config G c→ℝ} {D : Allocation G S x w} {J : ChartRatio G}
    (E : α→ Rim R'.p.threshold G c)
    (he : Opacity R R' p A hs hR ν (D:=D) (J:=J) e M l σ)
    (Ly : Lease S.patch.L R.p R'.p e M l σ y η)
    (hp : Resin R R' p A hs hR ν E e y)
local notation "X0"=> unmarked R R' p A hs (blink S) hR
local notation "G0"=> germ X0 A
local notation "R0"=> Gel.archived R (blank f) hR
local notation "Q"=> germinates R R' p A hs hR E
local notation "V0"=> courtyard R R' p A hs hR E
local notation "Λ0"=> (carves R R' p A hs hR E he (blank f) (blank c) (blink S))
local notation "Fl"=> (Empty.elim : Empty→Flake S G x L.park (blank c) R'.p.threshold)
local notation "wk"=> (Empty.elim : Empty→Prop)
local notation "Wp"=> (Empty.elim : Empty→ℝ)

structure ThresholdE (R : Rep G f) (s t A δ : ℝ) : Prop where
  sane : R.path.Bounds R.clip s t A
  valid : R.activities.RegularFamily R.p
  paid : R.activities.EBound R.p δ
  all a b : Nonempty (R.activities.Moves a b) -- even on K stuffing (may set trivial in empty builder)
include Ly hp he
set_option synthInstance.maxSize 512 in
set_option maxHeartbeats 600000 in
lemma emblazoned : Stripes R'.p V0 (fun _=>1) R'.p.supportExponent (1/M):= by
  obtain ⟨hT,hV⟩:= in_boxes R R' p A hs hR E he (blank f) (blank c) (blink S) Ly hp (fun _=>1) (fun _=>zero_lt_one)
  obtain ⟨z,v,hz,hb⟩:= commissioned R R' p A hs hR he (blank f) (blank c) (blink S) Ly (fun _=>1) (fun _=>zero_lt_one)
  have ht : Hits (zones X0) (bid z v Wp) R'.p (ucap e+1) (2*σ):= marches _ _ (incomes _ _ _ _ _ _ _ _ _ _ _ _ hz) hb (by unfold ucap; linarith only)
  let T':=Λ0
  let K:= picture R Q p R0 Fl A (show 25*radiusB x+30≤(Q).p.B from hs) (blink S)
  let G:= bequeath K A
  -- create auth directly on this Vac Rep. Transports not an estimate.
  have hh: LetterCost R Q p R0 Fl A hs (blink S) wk z v Wp l M (fun _=>1):= by
    exact ⟨hz.1,hz.2,hz.3,hz.4,hz.5,hz.6⟩
  let g:=Glaze R Q p R0 Fl A hs (blink S) wk
  have hx:rawRadii T' G g 1 e M l y 0:= finances _ _ _ _ _ _ _ _ _ _ _ _ T' hh Ly.lamps Ly.bright zero_lt_one hV Ly.coin ht Ly.inferno Ly.fees (fun i=>i.elim)
  let Y:=after G (measureH T') T'.pay
  have ha : Stripes (Q).p Y (fun _=>1) (e+1) (1/M):= (authenticity T' G g _ (fun _=>zero_lt_one) Ly.bright Ly.lamps Ly.coin Ly.resumes hx).2.2
  obtain ⟨H⟩:= (show Nonempty (Embedded T'.f G) from hT.rolls)
  obtain ⟨C⟩:= rainy G (measureH T') T'.pay H
  have hv : Stripes (Q).p V0 _ (e+1) (1/M):= pull_stripe _ C ha
  exact billed_again _ (show Stripes R'.p V0 (fun _=>1) _ _ from hv) Ly.output (fun _=> zero_lt_one)
set_option maxHeartbeats 400000 in
lemma sounded {ό θ c0 d : ℝ} (h : ThresholdE R' ό θ c0 d) (hx : 1/M ≤ v) : (Q).Lawful ό θ c0 d v:= by
  let A1:= V0; let V:= Q
  have hb : ∀ i:(Λ0).D,((Λ0).f i).fires= quiet _:= Vac.debt _
  have hz i:(V0 i).fires=quiet _:= blanking (blanking hb (fun _=>rfl)) (fun _=>rfl) i
  have hA:= burnCost R' V0 (emblazoned R R' p A hs hR E he Ly hp) hz
  obtain ⟨m,hm,hH⟩:=hA; refine ⟨h.sane,⟨⟨h.valid.smooth,h.valid.at_flat,h.valid.vanish⟩,plenty _ (seated R' V0) (fun i=> (prepare (bareBurst ∘ A1) i).choose_spec.1) _ _ ,travelers R R' p A hs hR E he hp h.all,h.paid,m,hm,fun i=>?_⟩⟩
  exact ⟨(hH i).1,(hH i).2.1,(hH i).2.2.trans hx⟩

omit hp he Ly in
include A in
set_option maxHeartbeats 400000 in
lemma push_empty (U : Config G c) :
    S.push R.beta (Value.dust R (Empty.elim : Empty→SourceAt G (blank f)) R0) U=scalar Empty (S.push R.beta R.eval U):= by
  rw [darkDust R hR _ _ (conservation R (blank f) hR) (fun _=>rfl)]
  let f:= LinearMap.toContinuousLinearMap ({ toFun:=scalar Empty, map_add':=map_add _,map_smul':=fun z x=>by change scalar _ (z * x)=_; rw [map_mul]; exact (by rw [RingHom.id_apply,← Complex.coe_smul,Algebra.smul_def]; rfl) } : ℝ →ₗ[ℝ] veil Empty)
  unfold StepData.push; change _= f _; rw [← f.integral_comp_comm]; exact integral_congr_ae (Filter.Eventually.of_forall fun x=> (f.map_smul ..).symm); exact StepData.push_slice (S.isKernel A.produced.branched _) U _ ((R.envelope hR).integrable _)
omit hp in
lemma unmarked_push (h : Coupler T L J D R.beta) :
    S.push R.beta (Value.dust R (Empty.elim : Empty→SourceAt G (blank f)) R0)=
      bouys («Q»:=R') (fun x=>↑(ν x)) G0 (bequeath X0 A):= by
  obtain ⟨z,v,hz,_⟩:= commissioned R R' p A hs hR he (blank f) (blank c) (blink S) Ly (fun _=>1) (fun _=>zero_lt_one)
  let E₀ := (Empty.elim : Empty → SourceAt G (blank f))
  have ha : earns_layout X0 T:= fun i U H k=> (refund _ _ _ _ _ _ _ _ _ _ _ _ hz (fun _=> zero_lt_one) Ly.lamps Ly.bright i U k H).1
  have ht': Light R E₀ R0 (fun _=>1) R.p.supportExponent 0 η:=by refine ⟨⟨fun _=>0, (fun i=>i.elim),fun i=>i.elim⟩,sticker R _ hR _⟩
  funext i; have hπ:=brigade A R' (picture R R' p R0 Fl A hs (blink S)) i (fun x=>↑(ν x)); refine (rendered X0 (dust_env R E₀ R0 (fun _=>zero_lt_one) R.p.exponent_pos.le hR ht' (conservation R (blank f) hR)) (dust_gauge R E₀ R0 hR) A h ?_ ha i).trans (show _ from hπ)
  exact fun A' V hv=> stage_gain R R' p R0 Fl A hs (blink S) E₀ (by intro V A' k z; rw [Fintype.sum_empty,Next.Rank.Exponential.pass_zero,Fintype.prod_empty]) he.roofs V hv
omit hp in
lemma clear_stencil (h : Coupler T L J D R.beta) (U : Config G c) (hx : flags R'.p.threshold U=∅): ν U * realGas G0 R'.p ∅ U=S.push R.beta R.eval U :=by
  let X:= Inn X0; let S':= bequeath X0 A; let g(t:Finset X):=(∏ i∈t,(S' i).tolls U)* backgroundU G0 R'.p.threshold (t.biUnion fun i=> (S' i).extent) U
  apply scalar_inj Empty; rw [← push_empty R A hR U,unmarked_push R R' p A hs hR he Ly h]; unfold bouys; rw [hx]
  have hp : univ.filter (fun t=> unmark S' t ∅)=({∅}:Finset (Finset X)):= by
    ext i; simp only [Finset.mem_filter, Finset.mem_singleton, mem_univ,true_and]; constructor
    · intro he
      by_contra H
      obtain ⟨j,hj⟩:=nonempty_iff_ne_empty.mpr H; obtain ⟨x,hx⟩:= (gruel X0 A (callsQuiet R R' p A hs hR (blink S)) j).needed
      have hx : x∈i.biUnion (fun i=> (S' i).inventory):= mem_biUnion.mpr ⟨_,hj, (show (S' j).inventory=(gruel X0 A (callsQuiet R R' p A hs hR (blink S)) j).inventory from congr_arg _ (held_guests _ _ (callsQuiet R R' p A hs hR (blink S)) _)) ▸ hx⟩
      rw [he.2] at hx; simp at hx
    rintro rfl; constructor
    · intro i h; simp at h
    simp
  change _=(↑(ν U):ℂ) • (∑ t∈ univ.filter (fun t=> unmark S' t ∅),g t)
  have he i V : (G0 i).value V=((((G0 i).value V).re:ℝ):ℂ) :=worth_real R R' p A hs hR he (blank f) (blank c) (blink S) i.val V
  rw [hp, Finset.sum_singleton]; unfold g; rw [Finset.biUnion_empty,prod_empty,one_mul,evening_table _ _ (fun i=> (parch X0 A i).1) he,map_mul,Algebra.smul_def]; rfl

set_option maxHeartbeats 500000 in
lemma perceived (h : Coupler T L J D R.beta) {ό θ c0 d v : ℝ} (hX : (Q).Lawful ό θ c0 d v) : (Q).eval=S.push R.beta R.eval:= by
  obtain ⟨hT,hV⟩:= in_boxes R R' p A hs hR E he (blank f) (blank c) (blink S) Ly hp (fun _=>1) (fun _=>zero_lt_one)
  let S':= bequeath X0 A
  let K:= Λ0
  let E₀ := (Empty.elim : Empty → SourceAt G (blank f))
  have hC : Matric K S' (S.push R.beta (Value.dust R E₀ R0)):= by
    have hX : S.push R.beta (Value.dust R E₀ R0)= bouys («Q»:=Q) (fun x=>↑(ν x)) G0 S':= unmarked_push R R' p A hs hR he Ly h
    rw [hX]; exact in_bulk _ _ _ _ hT.pays hT.rolls
  let D':=bequeath X0 A
  let U(i : Inn X0):Prop := False
  obtain ⟨H,H'⟩:= sunny_pass K D' _ hC U
  let F:= Sum.elim (downstairs K D' U) (upstairs K D' U); let Y:=after D' (measureH K) K.pay
  -- Empty marker set: all B columns reduce by archived group
  have htS (i) : (Y i).fires=quiet _:= by
    apply Subtype.ext; ext z; exact z.elim
  let X:= Bottom K D' U ⊕ Top K D' U
  haveI : IsEmpty X:=⟨fun t=> by obtain ⟨x,h⟩:= (F t).chosen; exact x.elim⟩
  have hv': S.push R.beta (Value.dust R E₀ R0)= (scalar Empty) ∘ (Q).eval:=Eq.trans H (darkDust Q hX F Y H' htS)
  ext1 i; apply scalar_inj Empty; rw [← show _=scalar Empty ((Q).eval i) from congr_fun hv' i]; exact push_empty R A hR i
end closure
end YM.PhysicalNext.InteractingRank.Display.Sew
