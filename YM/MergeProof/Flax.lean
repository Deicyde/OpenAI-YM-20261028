import YM.MergeProof.Buys
import YM.MergeProof.Palette
import YM.MergeProof.Pitch
import YM.MergeProof.Spread
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Deck.Tangent
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Menu
open Function Filter Lattice Wilson RG MeasureTheory Finset Push Local Extra.Histories PhysicalNext.Repeat Lotus Merge Merge.Palette Accent Marker
open Extra.Multi GridApprox.Nil
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {V ι β : Type}[DecidableEq V] {B:Census V} {G:Gauge}{f c:Side}{R:Rep G f}{E:Rep G c}
open MeasureTheory Extra.Trajectories 
variable [Fintype ι](q:ι→ Hat B R) (S:StepData c f)
set_option quotPrecheck false
local notation "M0"=> fun i=> (q i).M
local notation "w"=> Palette.sign M0 S
local notation "a"=> R.activities
local notation "u"=> logDeck q
variable {v:V→ℝ}(h:∀ i,0<v i)

-- tickets grouped Wing; evaluate weekly receipts
lemma ink (k:ℕ)(p:Tickets (Palette.sign (fun i=>(q i).M) S)): k∈(team (fun i=>(q i).M) p).gasDue↔ (Wing.gasKey k).badge S∈p.reach:=by
   rw [Team.asked,←label]; unfold Team.signs
   constructor
   · rintro ⟨i,hi,h⟩; exact mem_image.mpr ⟨i,hi,congr_arg (fun wing : Wing=> wing.badge S) h⟩
   intro hx; obtain ⟨i,hi,h⟩:= mem_image.mp hx; exact ⟨i,hi,Team.badged S h⟩
-- Master retail at one U: payload exact via expansion of degree finite old support and each logDeck.
variable (U:Config G f)

def Kunt (j:ℕ)(U:Config G f): Poly B:= Poly.bead B (↑(R.activities.K j U):ℂ) + rush q (.gasKey j) U
def jets (U:Config G f): Poly B:=∏ i∈ (logDeck q), (1+rush q (.logKey i) U)
-- box support Wing lift sites: no log vacancy required beyond p.M. Use directly Badge S
def bunch (z:Finset ℕ):= ((logDeck q).image (fun i=> (Wing.logKey i).badge S)) ∪ (z.image fun i=> (Wing.gasKey i).badge S)
local notation "c₀"=> Poly.bead B
lemma bunchy (b:Finset ℕ) (p:Tickets (w)): p.reach ⊆ bunch q S b ↔ (team M0 p).gasDue ⊆ b:=by
   constructor
   · intro h j hj; obtain hj|hj:= mem_union.mp (h ((ink q S j p).1 hj))
     · obtain ⟨i,hi,h'⟩:= mem_image.mp hj; cases Team.badged S h'
     obtain ⟨i,hi,h'⟩:=mem_image.mp hj; exact Wing.gasKey.inj (Team.badged S h') ▸ hi
   intro h j hj; obtain ⟨i,hi,hj⟩:=mem_image.mp hj; have ht : (WKey (q i)).badge S=j:=hj -- notation edit
   cases hx: WKey (q i) with
   | logKey k=>rw [hx] at ht; exact mem_union_left _ (mem_image.mpr ⟨k,(cams q k).2 ⟨i,hx⟩,ht⟩)
   | gasKey k=> rw [hx] at ht; exact mem_union_right _ (mem_image.mpr ⟨k,h ((ink q S k p).2 (ht.symm ▸ (hj ▸ p.reaches_of hi))),ht⟩)

include h
local notation "r"=> fun i=> sumFee (q i) v
local notation "z'"=> fun i=> sing (q i) v
local instance : IsTopologicalSemiring (Poly B):=⟨⟩
def ash (v:V→ℝ) (p:Tickets (Palette.sign (fun i=>(q i).M) S))(U:Config G f) (k: Finset ℕ): Poly B:= (↑((team (fun i=>(q i).M) p).bun k U * ∏ i∈p.val, sumFee (q i) v):ℂ) • ∏ i∈p.val,sing (q i) v
private def verb (j:Wing): Poly B:= match j with
   | .gasKey i=> Poly.bead B (↑(R.activities.K i U):ℂ)
   | .logKey _=> 1
omit [Fintype ι] in
lemma convert_p (U : Config G f) (p:Tickets (w)) : (↑((team M0 p).ingredients U * ∏ i∈p.val,r i):ℂ) • (∏ i∈p.val,z' i)= ∏ i∈p.val,amount (q i) U:=by
   let t:= M0
   rw [show (team t p).ingredients U=∏ i∈p.val,(t i).ingredient U from ?_,Complex.ofReal_mul,mul_smul]; let F' i:=amount (q i) U
   let A':= t
   have he i:amount (q i) U= (↑((t i).ingredient U):ℂ) • ((↑(sumFee (q i) v):ℂ) • z' i):= by rw [purchase _ h]; rfl
   simp_rw [he]; rw [Finset.prod_smul, Finset.prod_smul]; push_cast;rfl
   unfold Team.ingredients; exact Finset.prod_image (fun i hi j hj h'=> p.prop hi hj (congr_arg (fun L:Lotus.Leaf R=> L.turn.badge S) h'))
lemma cliff (k:Finset ℕ): jets q U * (if R.activities.admissible R.p U k then ∏ i∈k,Kunt q i U else 0)=∑ i, ash q S v i U k:=by
   by_cases ht:R.activities.admissible R.p U k
   swap; · rw [if_neg ht,mul_zero]; symm; exact sum_eq_zero fun i _=> by unfold ash Team.bun; rw [if_neg ht,zero_mul,Complex.ofReal_zero,zero_smul]
   rw [if_pos ht]; let d(j:Wing):= verb (R:=R) (B:=B) U j; let F':= Function.extend (fun i:Wing=> i.badge S) d 0; let f i:= amount (q i) U; let P j:= F' j+Tickets.extra (w) f j
   have hp(i):F' (i.badge S)=d i:= (Team.badged S).extend_apply ..
   have hq (j:Wing):Tickets.extra (w) f (j.badge S)=rush q j U:=by unfold Tickets.extra rush; simp_rw [show ∀ i:ι, Palette.sign M0 S i=j.badge S ↔ WKey (q i)=j from fun i=> (Team.badged S).eq_iff]; congr!
   let x(i:ℕ):=(Wing.logKey i).badge S; let y(i:ℕ):=(Wing.gasKey i).badge S
   let A:= (logDeck q).image x; let C:= k.image y; have H: Disjoint A C:=by apply Finset.disjoint_left.mpr; intro i ha hb; obtain ⟨j,hj,rfl⟩:=mem_image.mp ha; obtain ⟨l,hl,hℓ⟩:= mem_image.mp hb; cases Team.badged S hℓ
   have hz : ∏ i∈ (bunch q S k), P i= jets q U * ∏ i∈k,Kunt q i U :=by
      unfold bunch jets Kunt; rw [prod_union H,prod_image (fun i hi j hj he=> Wing.logKey.inj (Team.badged S he)),prod_image (fun i hi j hj he=> Wing.gasKey.inj (Team.badged S he))]; unfold P; simp_rw [hp,hq]; rfl
   rw [← hz,Tickets.expanded]; apply sum_congr rfl; intro p _; unfold ash Team.bun; rw [if_pos ht]; by_cases he:p.reach⊆ bunch q S k
   swap; · rw [if_neg he,Team.bill,if_neg ((bunchy q S k p).not.1 he),zero_mul,Complex.ofReal_zero,zero_smul]
   rw [if_pos he,Team.bill,if_pos ((bunchy q S k p).1 he)]
   let M:= team M0 p; let Y:= k\M.gasDue
   have hP: ∏ i∈ (bunch q S k)\p.reach,F' i=Poly.bead B (↑(∏ i∈ Y,R.activities.K i U):ℂ):=by
      let P:= p.reach; have hV: (A\P)∪ (C\P)=(bunch q S k) \ P:= (Finset.union_sdiff_distrib ..).symm -- check
      rw [← hV, prod_union (Finset.disjoint_left.mpr fun i hi hj=> Finset.disjoint_left.mp H ((mem_sdiff.mp hi).1) ((mem_sdiff.mp hj).1))]; rw [Finset.prod_eq_one (s:=A\P) (fun i hi=>?_ ),one_mul]
      · have hc:C\P= Y.image y:=by ext i; constructor
                                   · intro hi; obtain ⟨ha,hb⟩:=mem_sdiff.mp hi; obtain ⟨j,hj,rfl⟩:=mem_image.mp ha; exact mem_image.mpr ⟨j,mem_sdiff.mpr ⟨hj,mt (ink q S j p).1 hb⟩,rfl⟩
                                   intro hi; obtain ⟨j,hj,rfl⟩:=mem_image.mp hi; obtain ⟨hj,hp⟩:=mem_sdiff.mp hj; exact mem_sdiff.mpr ⟨mem_image_of_mem _ hj,mt (ink q S j p).2 hp⟩
        rw [hc,prod_image (show Injective y from fun i j he=> Wing.gasKey.inj (Team.badged S he)).injOn,Complex.ofReal_prod,map_prod]; exact prod_congr rfl fun i _=>hp _
      obtain ⟨k,hk,rfl⟩:= mem_image.mp (mem_sdiff.mp hi).1; exact hp _
   rw [hP, mul_comm _ (Poly.bead B _),Poly.product_bead, show (∏ i∈p.val,f i)= _ from (convert_p q S h U p).symm, ← mul_smul]; congr 1; push_cast; ring
end YM.MergeProof.Menu
