import YM.MergeProof.Garden
import YM.MergeProof.TeamWorld


set_option autoImplicit false
noncomputable section
namespace YM.Merge.Palette
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Contract Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse
open Coat Matter ProbabilityTheory Poll Pond PhysicalNext.Repeat PhysicalNext.Repeat.Lotus Greenbelt
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {ι : Type} [Fintype ι] {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ E Λ μ x κ w C : ℝ} {Ñ:ChartRatio G}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
variable (M:ι→Lotus.Leaf R)(Y:Cash W x μ L Q o C T R) (χ:Chi)
local notation "sx"=> radiusB x
open Blaze.March Multiple Ursell Trees Mixed Daisy OmitClusters Gas
variable (rA:ι→ℝ)
local notation "X'"=> swing Q L μ R.beta x C

variable (hR:Plot M Y rA) {e d B:ℝ} {j k : ℕ} (hB: Bikes Q L μ x a e B j k)
set_option quotPrecheck false
--
local notation "p₀"=> fun i:Y.ThinP=> tune M Y rA 0 k i.val
local notation "p₁"=> fun i:Y.ThickP=> tune M Y rA 1 0 i.val
local notation "P₀"=> pledgeA L Q μ x B j k
local notation "P₁"=> Charity.daisD Q L μ x k
local notation "VQ" => pledgeQ L Q μ x B j k
local notation "E0" => Q.mark L μ x
local notation "ρ"=> sailUp Q L x

omit [Fintype ι] in
lemma quiet (p:Molecule S)(U:Config G c): act M Y χ U p (Tickets.none _)= Y.spawn χ U p:=by
  let V:=team M (Tickets.none (sign M S)); have hV:V.own=∅:=by simp [V,team,Tickets.none]
  have hp {F:Forest S.ratio} (X:Coat T F): V.into X W o.a Q.table (own p) Q.halo p = X.body R Q.table W o.a (own p) Q.halo p:= by
    unfold Team.into Team.premium Team.signs Team.paidU; funext x; simp_rw [hV,Finset.image_empty,Finset.prod_empty, one_mul,sdiff_empty];rw [if_pos (empty_subset _)]; rfl
  refine congr_arg likely (funext fun i=>?_); let X:= prism T x χ o.K U (allot i)
  change V.bloom X W o.a Q.table Q.halo p=proceedsA R X W o.a Q.halo Q.table p
  unfold Team.bloom proceedsA;split; · exact congr_arg likely (funext fun j=>by unfold Team.tithe Coat.attains; rw [hp]) -- annotate measure
  rfl
lemma muted (U: Config G c) : color M Y χ U (fun _=>0)= Y.spawn χ U:=by
  funext i; unfold color; rw [sum_eq_single (Tickets.none _),quiet]; · simp [Tickets.none] -- prod empty
  · intro j hj hp; obtain ⟨k,hk⟩:= Finset.nonempty_iff_ne_empty.mpr (show j.val≠ ∅ from fun hx=>hp (Subtype.ext hx)); rw [prod_eq_zero hk (rfl),zero_mul]
  simp
lemma springs (V:Config G c)(i : Molecule S)(z : ι→ℝ)(hp: color M Y χ V z i ≠0) : Ac.Spark Y.supportP i ∧ (roster i).flags=RG.flags (Pressure.temp x) V∩Y.unionP i ∧ (Y.unionP i).Nonempty:= by
  letI:Nonempty (Forest S.ratio):= Tree.select S.ratio S.patch.odd_side
  obtain ⟨p,h⟩:∃ p,act M Y χ V i p≠0:=by by_contra! hn; apply hp; unfold color; simp_rw [hn,mul_zero,sum_const_zero]
  obtain ⟨hv,he⟩:= present M Y χ V p i (F:= Classical.ofNonempty) h
  have hf : Ac.Spark Y.supportP i:=he.1; refine ⟨hf, he.2.2.symm,?_⟩
  by_cases hh:p.val.Nonempty
  swap
  · have hr:p=Tickets.none _:=Subtype.ext (Finset.not_nonempty_iff_eq_empty.mp hh); rw [hr,quiet] at h; exact (Y.resident χ V _ h).2.2.1
  obtain ⟨a,h⟩:= hh
  let m:=M a; have hpL:=m.turn.badge_area R T Q.halo (radiusB x)
  have hu : enlargement S.ratio Q.halo (radiusB x) (RG.inspected m.crest)⊆Y.unionP i:= hpL ▸ (show areas R T Q.halo (radiusB x) _ ⊆ Y.unionP i from subset_biUnion_of_mem _ (hv (p.reaches_of h)))
  refine Finset.Nonempty.mono hu (Finset.Nonempty.mono (halo_subset _ _) (Finset.Nonempty.image ?_ _)) -- edit
  suffices H:m.crest.Nonempty from H.mono subset_union_left
  unfold Leaf.crest; cases m.turn
  · exact ⟨_,(R.activities.reg _).anchor⟩
  exact ((R.activities.forced _).inventory_ne).mono (R.activities.forced _).inventory_sup

lemma color_spin (θ : ι→ℝ)(i : Molecule S) : Measurable (fun V=> color M Y χ V θ i) ∧ UsesFinal (Pressure.temp x) (Y.unionP i) (fun V=> color M Y χ V θ i) ∧ GaugeInvariant (fun V=> color M Y χ V θ i):=by
  have he(p:Tickets (sign M S)):= (team M p).spinning T x χ Y i
  exact ⟨Finset.measurable_fun_sum _ (fun j _=> measurable_const.mul (show Measurable (fun V=> act M Y χ V i j) from (he j).2.2)),fun V U h hx=> sum_congr rfl fun j _=>congr_arg (_ * ·) ((he j).1 V U h hx),fun t U=> sum_congr rfl fun j _=>congr_arg (_ * ·) ((he j).2.1 t U)⟩
open Blaze Refrain Letter OmitClusters
variable (θp:ι→ℝ) (V:Config G c)
lemma smiling (p:Y.Chainbook):
    let g:= fun V=> Y.smilesMill V (color M Y χ V θp) p
    Measurable g∧ UsesFinal (Pressure.temp x) (Y.library p) g∧ GaugeInvariant g ∧ (g V≠0→ (Y.inventory p.1.toLeft).Nonempty∧ Y.statesPool V p∧Ac.Spark Y.bookFoot p.1):=by
  intro g
  let Z:= fun V i=> Y.cologneMill (color M Y χ V θp) i; have hg(i:Y.Chapter): Measurable (fun V=> Z V i) ∧ UsesFinal (Pressure.temp x) (Y.bookFoot i) (fun V=>Z V i)∧GaugeInvariant (fun V=>Z V i):=by
    rcases i with i|i
    · exact color_spin M Y χ θp i.val
    let u V j:= Y.entriesMill (color M Y χ V θp) (i.2 j); let a:ℝ:=Ursell.coefficient Y.seam i.2
    have h(z): Y.smallAt (i.2 z)⊆ Y.bookFoot (.inr i):= subset_biUnion_of_mem (Y.smallAt ∘ i.2) (mem_univ _)
    refine ⟨(Measurable.neg ( (measurable_const (a:=a) |>.mul (Finset.measurable_fun_prod _ fun p _=> show Measurable (fun V=>u V p) from (color_spin M Y χ θp _).1)).div_const ((i.fst+1).factorial:ℝ))),fun V U hV hb => ?_,fun t U=> ?_⟩
    · exact congr_arg (fun v:ℝ=>-(a*v/↑(i.1+1).factorial)) (prod_congr rfl fun j _=> inheritance ((color_spin M Y χ θp _).2.1) (h j) V U hV hb)
    exact congr_arg (fun v:ℝ=>-(a*v/↑(i.1+1).factorial)) (prod_congr rfl fun j _=> (show u (gauge t U) j=u U j from (color_spin M Y χ θp _).2.2 t U))
  refine ⟨?_ ,?_,?_,?_⟩
  · by_cases hv:Y.Fresh p∧ Ac.Spark Y.bookFoot p.1
    · let q(V : Config G c):=RG.flags (Pressure.temp x) V
      unfold g Cash.smilesMill; refine Measurable.ite ?_ (Finset.measurable_fun_prod _ (fun i _=>(( (hg i.val).1).pow_const _).div_const _)) measurable_const
      rw [show {V:Config G c| _}= ⋃ t∈ univ.filter (fun t=> Y.inventory p.fst.toLeft=t∩Y.library p),{V : Config G c|q V=t} from Set.ext (fun V:Config G c=> by simp [hv.1,hv.2,Cash.statesPool,q])]
      exact MeasurableSet.iUnion fun i=>MeasurableSet.iUnion fun _=>RG.flags_measurable_eq ..
    have ht : g=fun _=>0 := funext fun i=> if_neg (fun hx=>hv ⟨hx.1,hx.2.1⟩)
    rw [ht]; exact measurable_const
  · intro V U hv hl; unfold g Cash.smilesMill; have hu : Y.statesPool V p↔ Y.statesPool U p:=by unfold Cash.statesPool; rw [inter_comm, hl,inter_comm]
    simp_rw [hu]; split
    · exact prod_congr rfl fun i _=> congr_arg (fun t:ℝ => t^(p.2 i+1)/↑(p.2 i+1).factorial) (inheritance ((hg i.1).2.1) (subset_biUnion_of_mem Y.bookFoot i.2) _ _ hv hl)
    rfl
  · intro t V; have hF : Y.statesPool (Lattice.gauge t V) p↔Y.statesPool V p:= by unfold Cash.statesPool; rw [gauge_flags]
    unfold g Cash.smilesMill; simp_rw [hF]; split
    · exact prod_congr rfl fun i _=> congr_arg (fun t:ℝ=> t^(p.2 i+1)/↑(p.2 i+1).factorial) ((hg i.val).2.2 t V)
    rfl
  intro hc; unfold g Cash.smilesMill at hc; split at hc
  next h=>
    obtain ⟨i,hi⟩:= Y.regains p h.2.1 h.1
    exact ⟨Finset.Nonempty.mono (subset_biUnion_of_mem (fun i=> (roster (i:Y.ThickP).val).flags) (mem_toLeft.mpr hi)) i.2.2,h.2.2,h.2.1⟩
  next => exact (hc rfl).elim

end YM.Merge.Palette
