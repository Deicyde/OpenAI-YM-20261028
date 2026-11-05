import YM.FullVolume.Mark.Curses
/-! Affine cuts and jagged directions. Bill actual Trigger pins, complete labels before taking derivative of projection.
 Keep Statement Cap.Ne.` only occupied & unused admitted domain; E norms include off-mask germs at Equality. No claims outside Valid purpose.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Matric
open Finset Function Filter Set MeasureTheory Lattice Wilson RG Source Labels Extra.Histories Bid
open Planned.GuardedAtom Push Local Guard Motion PhysicalNext.Repeat Lotus
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{d:ℕ}{F:Labels.Frame G d}{B:SectionData F}{H:History G} {N p m:ℕ} {Y:Hol G}
section
variable {n:Side}{R:Rep G n}{T : SectionData F}{c₀ c₁ c₂:ℝ}
structure Gate (P:Coefficient F n)(R:Rep G n)(Y:Hol G)(k ζ:ℝ):Prop where
   first : orbitCost F * F.coeffSize P.x ≤ ζ
   earns : P.Format 0 Y R
   income : ∃ a b : ℝ, Tab P 0 R k a b ∧ turnCost R.p.order R.p.power * a+b ≤ ζ
variable {n' : Side} (P: Plate F n n')
structure Pros (X Z:Pin F n)(B:BudgetPoint): Prop where
   point : X.1=Z.1
   force : X.2.2=Z.2.2
   germs (j:ℕ):∀ y c,B.supBounds 0 (mapSeat j) (Z.2.1 j) y → y ≤ c → B.supBounds 0 (mapSeat j) (X.2.1 j) c
structure Afford (A:Hol G)(R:Rep G n)(R':Rep G n'):Prop where
   reg j (f g : Config G n→ℂ){x y:ℝ}: RegFit R 0 d A (mapSeat j) f →RegFit R 0 d A (mapSeat j) g→ R.p.supBounds 0 (mapSeat j) f x→ R.p.supBounds 0 (mapSeat j) g y → (tell (P.tint j f-P.tint j g)).Format 0 A R' ∧ Pros (P.tint j f-P.tint j g) (P.tint j (f-g)) R'.p
   force j (f g : Config G n→ℂ){x y:ℝ}: SlotFit R 0 j f→SlotFit R 0 j g→(∀ V,‖f V‖ ≤ x)→ (∀ V,‖g V‖≤y)→ (tell (P.ink j f-P.ink j g)).Format 0 A R' ∧ Pros (P.ink j f-P.ink j g) (P.ink j (f-g)) R'.p
namespace Gate
variable {P:Coefficient F n}{k ζ:ℝ} {ι:Type}[Countable ι]
lemma weaker (h:Gate P R Y k c₀)(he:c₀≤c₁):Gate P R Y k c₁:= ⟨h.first.trans he,h.earns, let ⟨a,b,hp,h'⟩:= h.income; ⟨a,b,hp,h'.trans he⟩⟩
local notation "L"=> turnCost R.p.order R.p.power
lemma rem (h:Gate P R Y k ζ): P.remBound 0 R k ζ:= by
   obtain ⟨a,b,hv,he⟩:=h.income; have ht: 1≤L:=one_le_pow₀ (one_le_mul_of_one_le_of_one_le one_le_two (one_le_pow₀ one_le_two)); exact hv.bound ((add_le_add_left (le_mul_of_one_le_left hv.first ht) b).trans he)
lemma together (h:0<k)(f:ι→ Coefficient F n){v:ι→ℝ}(hs:Summable v)(hx:∀ i,Gate (f i) R Y k (v i))(e:ℕ≃ι×ℕ): Gate (Extra.Histories.merge e f) R Y k (∑' i,v i):=by
    choose a b ha hb using fun i=> (hx i).income
    have ht : 1 ≤ turnCost R.p.order R.p.power:= one_le_pow₀ (one_le_mul_of_one_le_of_one_le one_le_two (one_le_pow₀ one_le_two))
    have hv:Summable a:= .of_nonneg_of_le (fun i=>(ha i).first) (fun i=> (le_mul_of_one_le_left (ha i).first ht).trans ((le_add_of_nonneg_right (ha i).second).trans (hb i))) hs
    have hq:Summable b:= .of_nonneg_of_le (fun i=>(ha i).second) (fun i=> (le_add_of_nonneg_left (mul_nonneg (zero_le_one.trans ht) (ha i).first)).trans (hb i)) hs
    let X i:= (f i).x; have hO:= orbitCost_one_le F;have hg : Summable (fun i=> F.coeffSize (X i)):= .of_nonneg_of_le (fun i=>Work.G08.size_nonneg F _) (fun i=> (le_mul_of_one_le_left (Work.G08.size_nonneg F _) hO).trans (hx i).first) hs
    refine ⟨?_,merge_format e f (fun i=>(hx i).earns),∑' i, a i,∑' i,b i,(merge_tab e f h ha hv hq).1,?_⟩
    · refine (mul_le_mul_of_nonneg_left (Size.bound F hg) (zero_le_one.trans hO)).trans ?_; rw [← tsum_mul_left]; exact (hg.mul_left (orbitCost F)).tsum_le_tsum (fun i=> (hx i).first) hs
    rw [← tsum_mul_left, ← (hv.mul_left _).tsum_add hq]; exact ((hv.mul_left _).add hq).tsum_le_tsum hb hs
end Gate
end
local notation "A₀"=>H.rep N p m
local notation "A₁"=>H.rep N p (m+1)
local notation "s₀"=> H.S.side (m+1) p
local notation "s₁"=> H.S.side m p
local notation "Z"=> orbitCost F
local notation "μ"=>kappa H m
local notation "μ'"=> Real.sqrt (H.levels.clock.forcedAllowance (m+1))
variable {S:Desk G (H.S.side (m+1) p)}
variable (P:Tool F H N p m){D:GaugeDoor (H.rep N p (m+1)) (H.rep N p m)}{W:Worth}{T:Heading F}{c ε v t:ℝ}{X:Set Wing}
variable (hx:P.Cap B Y W D T c ε v X)(h:Well (H.rep N p (m+1)) S (Real.sqrt (H.levels.clock.forcedAllowance (m+1))))
open Extra.Histories.InputColumn
variable (i:F.Index)
local notation "J"=> Size.axis F i
local notation "u"=> tags P.plate P.up
variable (f g:Coin F Y S)
def gas (x₀:F.Index) (y:File G (H.S.side (m+1) p)): Listing→ Pin F (H.S.side m p):= u (book (Size.axis F x₀) y) x₀
def strip (u':File G (H.S.side (m+1) p)) : Listing→ Pin F (H.S.side m p):=
   consist 0 (fun i=> P.plate.tint i (u'.1 i)) (fun i=> P.plate.ink i (stowK P.up (book J u') i)) -- u macro conflicts
local notation "d₁"=> Matric.strip P i
local notation "d₂"=> gas P i
include hx h
lemma tram: ∃ r:Listing→ℝ,SumBudget r (ε*‖f‖) ∧ ∀ j:Listing, Gate (tell (strip P i (Coin.uses f) j)) A₀ Y μ (r j):=by
    let A:= P.plate; let K:= P.up; let V:=book J (Coin.uses f); let Q:=rack P.up V; let w:= (H.rep N p (m+1)).p; let F₀:= P.plate; let S₁:=d₁ (Coin.uses f)
    obtain ⟨hc,hv⟩:= granted h Y J f
    have he:Q.Format 0 Y A₁:= rack_format P.up V hc; have hp:= keeps P.up V hv
    obtain ⟨a,b,h₁,h₂,hv,hμ,⟨E,hE,hM⟩,q,hq,hQ⟩:= hp
    let e(i:ℕ):=w.mass (V.support i) (E i); let k(i:ℕ):= w.mass ((H.rep N p (m+1)).activities.forced i).support (q i)/μ'
    have hg := hx.budget.epsilon; have hR:SumBudget k b:=by
       refine ⟨fun i=>div_nonneg (hq.1 _) hμ.le,hq.2.1.div_const _,?_⟩; unfold k; rw [tsum_div_const]; exact (div_le_iff₀ hμ).mpr (hq.2.2.trans_eq (mul_comm ..))
    let r:Listing→ℝ:= consist 0 (fun i=> ε*e i) (fun i=> ε*k i)
    have hr:HasSum r (0+ε*((∑' i,e i)+∑' i,k i)):= by rw [mul_add]; exact added ((show Summable e from hE.2.1).hasSum.mul_left ε) (hR.2.1.hasSum.mul_left ε)
    have hi {j:Listing}(he:S₁ j=0)(h:0≤r j):Gate (tell (strip P i (Coin.uses f) j)) A₀ Y μ (r j):=by
       have h' : strip P i (Coin.uses f) j=0:=he; rw [h']
       have hp:= (spanNone B H N p m Y X D (t:=r j) h (le_refl (0:ℝ))).earns; have hp':=hp.leadP; rw [sub_zero] at hp'; exact ⟨hp',hp.format,hp.future⟩
    have hv(j:Listing): Gate (tell (strip P i (Coin.uses f) j)) A₀ Y μ (r j):=by
       rcases j with i|i|j
       · exact hi rfl le_rfl
       · have hu:= (hx.copies.regular i (Q.regular i) (E i) ⟨he.smooth _, he.origin _, he.identity_null _,he.projects _⟩ (hM i)).earns
         have he' := hu.leadP; rw [sub_zero] at he'; exact ⟨he',hu.format,hu.future⟩
       · by_cases H₀ : Q.forced j=0
         · exact hi (j:=.inr (.inr j)) (show P.plate.ink j (Q.forced j)=0 from (congr_arg (P.plate.ink j) H₀).trans (hx.copies.blank j)) (mul_nonneg hg (hR.1 j))
         have H' : X (.gasKey j) :=by
            have hd: j∈ Set.range (cart K):= not_not.mp (fun h=> H₀ (pit K V h)); obtain ⟨j,rfl⟩:=hd; exact hx.cart _
         have hu:= (hx.copies.forced j (Q.forced j) (q j) H₀ H' ⟨he.invariant _,he.borel _,he.supported _,he.carried _,he.forcing _⟩ (hQ j).1 (hQ j).2).earns
         have he' := hu.leadP; rw [sub_zero] at he'; exact ⟨he',hu.format,hu.future⟩
    refine ⟨r,⟨fun i=>rem_nonneg (hv i).rem, hr.summable,?_⟩,hv⟩
    rw [hr.tsum_eq, zero_add]; exact mul_le_mul_of_nonneg_left ((add_le_add hE.2.2 hR.2.2).trans (by assumption)) hg
-- Sums for reassembly.K
lemma solace : Summable (fun k=>(tell (gas P i (Coin.uses f) k)).x) ∧ ∀ j V,Summable fun k=>(tell (gas P i (Coin.uses f) k)).forced j V:=by
    obtain ⟨r,hp,he⟩:= tram P hx h i f; let x:=tell ∘ d₁ (Coin.uses f)
    have hf: Set.Finite {k | gas P i (Coin.uses f) k ≠ d₁ (Coin.uses f) k}:=(Set.finite_singleton (.inl ())).subset (by
        rintro (⟨⟩|i|k) h; exact Set.mem_singleton _; exact (h rfl).elim; exact (h rfl).elim)
    have hb : Summable fun j=> (x j).x :=by
        apply Summable.of_norm; apply Size.series F; exact .of_nonneg_of_le (fun j=> Work.G08.size_nonneg F _) (fun j=> (le_mul_of_one_le_left (Work.G08.size_nonneg F _) (orbitCost_one_le F)).trans (he j).first) hp.2.1
    have hq:= (merge_budget (code _) x (Real.sqrt_pos.mpr (forcedPos H.levels m)) (fun i=> (he i).rem) hp.2.1).2.2
    constructor
    · apply hb.congr_cofinite; filter_upwards [show ∀ᶠ k in cofinite, ¬ (gas P i (Coin.uses f) k ≠d₁ (Coin.uses f) k) from hf.compl_mem_cofinite ] with k h; exact congr_arg (fun a=>(tell a).x) (not_not.mp h).symm
    intro j V; have hm:Summable fun i=> (x i).forced j V:= ((hq.summable V).prod_symm.prod_factor j)
    apply hm.congr_cofinite; filter_upwards [hf.compl_mem_cofinite] with k h; exact congr_arg (fun a=>(tell a).forced j V) ((not_not.mp h).symm)
-- sub operation
include h
lemma travels (ha:Afford P.plate Y (H.rep N p (m+1)) (H.rep N p m)) (j:Listing): let W:=gas P i (Coin.uses f) j- gas P i (Coin.uses g) j
    (tell W).Format 0 Y (A₀) ∧ Pros W (d₁ (Coin.uses (f-g)) j) (A₀).p:=by
    dsimp only; rw [map_sub]; let a:=book J (Coin.uses f); let b:=book J (Coin.uses g); let T:=P.up; obtain ⟨hf,hq⟩:= granted h Y J f; obtain ⟨hp,hg⟩:=granted h Y J g
    have hv:= rack_format T a hf;have hu:=rack_format T b hp; obtain ⟨p,U,hP,hF⟩:= rem_tabs.mp (keeps T a hq); obtain ⟨k,v,hV,hW⟩:= rem_tabs.mp (keeps T b hg)
    rcases j with j|j|j
    · change (tell (P.plate.main i - P.plate.main i)).Format 0 Y _ ∧ Pros (P.plate.main i-P.plate.main i) 0 _
      rw [sub_self]; exact ⟨(spanNone B H N _ m Y X D (t:=0) le_rfl (le_refl (0:ℝ))).earns.format, rfl,rfl,fun i y c he hc=> bound_weaken he hc⟩
    · obtain ⟨e,H,hH⟩:=hP.regular; obtain ⟨q,hQ,hY⟩:= hV.regular; exact ha.reg j (a.regular j) (b.regular j) ⟨hf.smooth _,hf.origin _,hf.identity_null _,hf.projects _⟩ ⟨hp.smooth _,hp.origin _,hp.identity_null _,hp.projects _⟩ (hH j) (hY j)
    obtain ⟨e,U,hH⟩:= hP.forced; obtain ⟨q,hQ,hY⟩:=hV.forced
    rw [show d₁ (Coin.uses f-Coin.uses g) (.inr (.inr j))=P.plate.ink j (stowK P.up (breakP a b) j) from rfl,cogent a b P.up hq hg]; exact ha.force _ (stowK P.up a j) (stowK P.up b j) ⟨hv.invariant _,hv.borel _,hv.supported _,hv.carried _,hv.forcing _⟩ ⟨hu.invariant _,hu.borel _,hu.supported _,hu.carried _,hu.forcing _⟩ (hH j|>.2) (hY j|>.2)
lemma socket (ha:Afford P.plate Y (H.rep N p (m+1)) (H.rep N p m)) : Gate (breakP (P.shot i (Coin.uses f)) (P.shot i (Coin.uses g))) A₀ Y μ (ε * ‖f-g‖):=by
    obtain ⟨r,hp,he⟩:= tram P hx h i (f-g); obtain ⟨hv,hq⟩:= solace P hx h i f; obtain ⟨hV,hQ⟩:= solace P hx h i g
    let Z' j:=gas P i (Coin.uses f) j- gas P i (Coin.uses g) j; let Y' j:= tell (Z' j)
    have g'(j):Gate (Y' j) (A₀) Y μ (r j):=by
       let X':=turnCost
       let E j:= strip P i (Coin.uses (f-g)) j
       obtain ⟨hV,hQ⟩:= travels P hx h i f g ha j
       obtain ⟨a,b,Hv,hθ⟩:= (he j).income
       have hz:(Y' j).x = (tell (E j)).x:= hQ.point
       obtain ⟨A,hA,hX⟩:=Hv.regular
       refine ⟨(hz.symm ▸ (he j).first: _), hV,a,b,⟨Hv.divisor,Hv.first,Hv.second,⟨_, hA,fun i=>hQ.germs i _ _ (hX i) le_rfl⟩,?_⟩,hθ⟩
       rw [show (Y' j).forced= (tell (E j)).forced from hQ.force]; exact Hv.forced
    have hh : Extra.Histories.merge (code _) Y'= breakP (P.shot i (Coin.uses f)) (P.shot i (Coin.uses g)):=by unfold Y' Z'; simp_rw [tell_br]; exact melt _ hv hV hq hQ -- hx
    rw [← hh]; exact (Gate.together (Real.sqrt_pos.mpr (forcedPos H.levels m)) _ hp.2.1 g' (code _)).weaker hp.2.2
end YM.MergeProof.Matric
