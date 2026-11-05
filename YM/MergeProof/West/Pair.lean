import YM.MergeProof.West.Leet
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Tapes.West
open Function Lattice Wilson RG Perch Atlas Rise Normal Ribbon Spindle Glyph Exponential MvPolynomial Camp Peak Station Ac Alarm Thirst Corona Value Relation Finset Marker
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius
open MeasureTheory Cells Edition
variable {G:Gauge}{N n p k q i d D:ℕ} {C:Family G} {R:Lead G C.S p}
   {b:ℝ} {c:Course C N p k}{x:Points n}{hk:i<k}{h:middle C.path.levels b k ≤ i}
   {T τ U ε g B Y L} (E:Mural (d:=d) c R x b hk h q T τ U ε)

def glare (B ε u : ℝ) (D n:ℕ) := n* (capZ B D u+1)^n * defect B ε u D + ε*((u^n)^2*Common.priced B (2*(n*D)))+n*ε + u^n*(ε*Common.priced B (n*D))
-- guard stack
variable (P: Manner n → poly (Chamber G C.S (i+1) p))
local notation "K"=> ViewFt C k b p d x hk

def fullG (w:List (ViewFt C k b p d x hk))(z:E.Θ):ℝ:=(w.map (fun j=> c_hance E j z)).prod
def fullQ (w:List (ViewFt C k b p d x hk))(z:E.Θ):ℂ:=(w.map (fun j=> traceFt E j (P j.val) z)).prod
def fullP (w:List (ViewFt C k b p d x hk)):=(w.map fun j=>P j.val).prod
lemma goalie (w:List (ViewFt C k b p d x hk)) (hp:∀ i∈w,t_ests x b hk T.2.val i (C:=C)): letI := E.M; Guarded (fullG E w) (w.length*ε^2) E.μ:=by
  letI := E.M; haveI:=E.initial.norm
  induction w with
  | nil=> exact ⟨fun z=>zero_le_one,fun _=>le_rfl,measurable_const,by simp [fullG]⟩
  | cons i l IH=>
    rw [List.length_cons,Nat.cast_add_one, add_mul,one_mul,add_comm _ (ε^2)]
    exact guards_mul (E.lives i (hp i (by simp))) (IH fun j hj=> hp j (by simp [hj]))
lemma measQ (w:List (ViewFt C k b p d x hk)): letI:= E.M; Measurable (fullQ E P w):=by
   letI:= E.M; induction w with
   | nil=>exact measurable_const
   | cons j l IH=>exact (primeFt E j (P j.val)).mul IH
variable (hx:roomTest C.path.levels b k p d q) (t:Metal b c R hk ε τ g B Y L) (Hv:Healthy g (d_olm x b q (walls (clim C.path.levels i)) c.allow hk.le T.1 T.2.val) U) (he: 0 < ε)(he':ε≤1)
   {r:ℝ} (hr:0≤r)
variable (H:∀ i, Poetic (P i)) (hs:∀ i,totalDegree (P i)≤ D) (hu:∀ i,coin (P i)≤ r) (hp:∀ u,∀ i'∈(P u).vars,spotFt b (i+1) d (show i+1≤k from hk) x u i' (C:=C))
include hx t he he' H hs hu hp hr
lemma jester (v:List (ViewFt C k b p d x hk))(hv:∀ i∈v,t_ests x b hk (C:=C) T.2.val i):
   let Q:= fullP (C:=C) P v
   let l:=v.length
   let u:=capZ B D r+1
   Q.totalDegree ≤ l*D ∧ Q.vars⊆sp_okes x b hk d T.2.val (C:=C)∧ coin Q ≤ r^l ∧
      ∀ z, 0< fullG E v z → ‖fullQ E P v z‖ ≤ u^l ∧
      ‖fullQ E P v z-r_ose E Q z‖ ≤ l*u^l*defect B ε r D := by
   have hf := t.grain; let u:= capZ B D r+1; let V:=sp_okes x b hk d T.2.val (C:=C) (p:=p)
   have hA : 1≤u:=le_add_of_nonneg_left (mul_nonneg hr (zero_le_one.trans (priced_up D hf)))
   have hY : 0≤ defect B ε r D:= by unfold defect; positivity
   induction v with
   | nil=>
     intro Q l U
     simp only [Q,fullP,List.map_nil,List.prod_nil,totalDegree_one, l,List.length_nil,zero_mul,le_refl,true_and,vars_one,Finset.empty_subset,pow_zero]
     simp [coin,fullQ,r_ose, carry]
   | cons j l IH=>
     let W:= fun i hi=>hv i (List.mem_cons_of_mem j hi); obtain ⟨hi,hX,hV,hG⟩:=IH W
     let F:=P j.val; let x':=fullP (C:=C) P l; have hJ:=hv j (List.mem_cons_self ..)
     have hh : F.vars⊆V:=fun i' h'=> Finset.mem_filter.mpr ⟨Finset.mem_univ _,j,hJ,hp _ i' h'⟩
     have hG' : fullP (C:=C) P (j::l)=F*x':=rfl
     intro X l' u'
     dsimp only [X,l']; rw [hG',List.length_cons]
     refine ⟨(totalDegree_mul F x').trans ((add_le_add (hs j.val) hi).trans (show D+ _ ≤ _ from (by simp [add_mul,add_comm]))), Finset.Subset.trans (MvPolynomial.vars_mul F x') (Finset.union_subset hh hX), (Rise.funds 0 zero_le_one F x').trans ((mul_le_mul (hu j.val) (show coin x' ≤ r^l.length from hV) (show 0 ≤ coin x' from Rise.sign _ _ zero_le_one) hr).trans_eq (pow_succ' ..).symm),?_⟩
     intro z hz; letI:= E.M; have h₁:0< c_hance E j z := pos_of_mul_pos_left hz ((goalie E l W).lower z); have h₂:0<fullG E l z:=pos_of_mul_pos_right hz ((E.lives _ hJ).lower _)
     have he:capZ B D r≤u:=le_add_of_nonneg_right zero_le_one
     obtain ⟨hf,hq⟩:=hG z h₂; obtain ⟨ha,Hf,Hs⟩:= t_alent E j F hx t ‹0<ε› he' hJ (H j.val) (hp j.val) (hs _) (hu _) z h₁
     let y:= traceFt E j F z; let a:=fullQ E P l z; let b:=r_ose E F z;let d':= r_ose E x' z; let c:=defect B ε r D
     have hC:l.length*c ≥ 0:=mul_nonneg (by positivity) hY
     change ‖y*a‖ ≤ u^(l.length+1) ∧ ‖y*a-r_ose E (F*x') z‖ ≤ (↑(l.length+1):ℝ)*u^(l.length+1)*c
     rw [norm_mul]; refine ⟨(mul_le_mul (ha.trans he) hf (norm_nonneg _) (zero_le_one.trans hA)).trans_eq (pow_succ' ..).symm,?_⟩
     rw [show r_ose E _ z=b*d' from map_mul ..,show y*a-b*d'=(y-b)*a+b*(a-d') by ring]; apply (norm_add_le ..).trans
     rw [norm_mul,norm_mul]; apply (add_le_add (mul_le_mul Hf hf (norm_nonneg _) hY) (mul_le_mul (Hs.trans he) hq (norm_nonneg (a-d')) (zero_le_one.trans hA))).trans
     have hv':c*u^l.length ≤ u^(l.length+1) * c:= (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hA (l.length.le_succ)) hY).trans' (mul_comm ..).le
     push_cast; rw [pow_succ]; rw [pow_succ] at hv'; linarith only [hv']

include Hv
lemma t_worn (w:List (ViewFt C k b p d x hk))(hW:∀ i∈w,t_ests x b hk T.2.val i (C:=C)):
   letI:= E.M
   let F:= fun z=> ((↑(fullG E w z):ℂ))*fullQ E P w z
   Integrable F E.μ ∧ ‖(∫ z, F z ∂ E.μ)-e_legance b c x hk h T U ((R i).read (fullP (C:=C) P w))‖ ≤ glare B ε r D w.length:= by
   letI:= E.M; intro p
   obtain ⟨ha,hL,hP,H⟩:= jester E P hx t he he' hr H hs hu hp w hW
   let M:=capZ B D r+1; have hm:0≤M:=add_nonneg (mul_nonneg hr (zero_le_one.trans (priced_up D t.grain))) zero_le_one
   let l:= w.length; have hf :=t.grain
   obtain ⟨ht,hV⟩:= combFt E hx t Hv he hL ha hP (fullQ E P w) _ ⟨goalie E _ hW,measQ ..⟩ (pow_nonneg hm l)
      (fun z hz=> (H z hz).1) (show 0≤ l*M^l*defect B ε r D by unfold defect; positivity) (fun z h=>(H z h).2)
   refine ⟨ht,hV.trans (le_of_eq ?_)⟩; unfold glare M l; field_simp
end YM.Next.Rank.Tapes.West
