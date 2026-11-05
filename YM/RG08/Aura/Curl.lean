import YM.RG08.Aura.Equality

/-! # From solved period pencils to literal directional cover curls -/
noncomputable section
namespace YM.RG08.Aura
open Function Lattice Laurent Pert.Bulk Forms Carrel Steam Rows RG Stationary Bloch Tack Anchor Spar Sedan Precision Finset Exterior Packets Ducat Mason Yamen
open YM.Next.Free YM.Planned.PrimaryIntegral295 Matrix
open scoped Classical Matrix BigOperators PowerSeries Topology
set_option autoImplicit false
variable {G:Gauge}{I:Type}

def diff (p:Cover→Axis→G.ColorIndex→ℝ)(x: Cover)(i j:Axis)(c:G.ColorIndex):ℝ:=p (x+step i) j c-p x j c

def lock (p:Cover→Axis→G.ColorIndex→ℝ):Prop:=∀ i j x c,diff p x i j c = diff p x j i c
abbrev menu (F:Kernel (Loc G 1) I)(p: Market I)(x:Cover)(i:Axis)(c:G.ColorIndex):ℝ:= F (x,coord i,c) p
private def stairs (f:Cover→ℝ)(x:Cover)(i:Axis):ℝ:= f (x+step i)-f x
private lemma rung (F:Cover→ℝ)(x:Cover)(a:TypeFace 2)(b:TypeFace 1):
 (∑' z:Cover,cobound 1 a b (z-x)*F z)=∑ i:Axis,Exterior.left ℝ 1 i a b * stairs F x i:=by
 simp_rw [← (Equiv.addRight x).tsum_eq (f:=fun z=>cobound 1 a b (z-x)*F z), show ∀ z:Cover,(Equiv.addRight x) z=z+x from fun z=>rfl,add_sub_cancel_right] -- simplify
 simp_rw [cobound,Finset.sum_mul]
 rw [Summable.tsum_finsetSum (by intro i _; apply summable_of_ne_finset_zero (s:=insert 0 {step i}); intro z hz;simp only [mem_insert,mem_singleton,not_or] at hz;simp [hz.1,hz.2])]
 apply Finset.sum_congr rfl; intro i _
 simp_rw [mul_assoc,sub_mul,ite_mul,one_mul,zero_mul]
 rw [tsum_mul_left];congr 1
 have h(j: Cover):Summable (fun z:Cover=>if z=j then F (z+x) else 0):=summable_of_ne_finset_zero (s:={j}) (by intro b hb;rw [if_neg (by simpa using hb)])
 rw [Summable.tsum_sub (h _) (h _),tsum_ite_eq,tsum_ite_eq,add_comm,zero_add];rfl

lemma paid_curl (F:Kernel (Loc G 1) I)(p:Market I)(x:Cover)(c:G.ColorIndex)(q:TypeFace 2) : Pert.Bulk.bind (heat G) F (x,q,c) p= ∑ i:Axis, if h:i∈q.val then parity q.val i ℝ * (F (x+step i,remove i q h,c) p-F (x,remove i q h,c) p) else 0:=by
 unfold Pert.Bulk.bind;rw [Fintype.sum_prod_type];simp only [Finset.sum_apply]; --
 change (∑ j:TypeFace 1,∑ k:G.ColorIndex,∑' z:Cover,(prism G.ColorIndex (plain (cobound 1)) (x,q,c) (z,j,k))*F (z,j,k) p)=_
 have he (j:TypeFace 1): (∑ k:G.ColorIndex,∑' z:Cover,(prism G.ColorIndex (plain (cobound 1)) (x,q,c) (z,j,k))*F (z,j,k) p)=∑' z:Cover,plain (cobound 1) (x,q) (z,j)*F (z,j,c) p:=by rw [sum_eq_single c (fun b _ hb=>by simp [prism,Ne.symm hb]) (by simp)];simp [prism]
 rw [Finset.sum_congr rfl fun i _=>he i]
 have hr (j): (∑' z:Cover,plain (cobound 1) (x,q) (z,j)*F (z,j,c) p)=∑ i:Axis,left ℝ 1 i q j*stairs (fun z=>F (z,j,c) p) x i:=rung ..
 simp_rw [hr];rw [Finset.sum_comm];apply Finset.sum_congr rfl;intro i _;change ((left ℝ 1 i) *ᵥ (fun j=>stairs (fun z=>F (z,j,c) p) x i)) q=_;rw [Exterior.eliminate];split <;> rfl

lemma scribe {F V:Kernel (Loc G 1) I}(he:Pert.Bulk.bind (heat G) F=Pert.Bulk.bind (heat G) V)(p:Market I): lock (menu (F-V) p):=by
 have hi(i j:Axis)(x:Cover)(c:G.ColorIndex)(h:i<j):diff (menu F p) x i j c-diff (menu F p) x j i c=diff (menu V p) x i j c-diff (menu V p) x j i c:=by
    let q:TypeFace 2:= ⟨{i,j},by simp [h.ne]⟩
    have hq(k) : k∈ q.val ↔ k=i ∨ k=j:=by simp [q]
    have hh (F:Kernel (Loc G 1) I):Pert.Bulk.bind (heat G) F (x,q,c) p=diff (menu F p) x i j c-diff (menu F p) x j i c:=by
       rw [paid_curl,← Finset.sum_subset (s₁:=q.val) (Finset.subset_univ _) (fun i _ hi=> dif_neg hi)];unfold q; rw [Finset.sum_pair h.ne]; simp only [mem_insert_self, Finset.mem_insert_of_mem (Finset.mem_singleton_self j), ↓reduceDIte]
       have hm:Finset.filter (· < i) ({i,j}:Finset Axis)=∅:=by ext x;simp [Finset.filter_insert];intro he;subst he;exact h.le
       have hi:Finset.filter (· < j) ({i,j}:Finset Axis)={i}:=by ext x;simp [h,Finset.filter_insert];intro he;subst he;exact fun hk=>False.elim (Std.Irrefl.irrefl _ hk)
       have hj : (remove j ⟨{i,j},show ({i,j}:Finset Axis).card=1+1 from by simp [h.ne]⟩ (by simp))=coord i:= by apply Subtype.ext; ext k; simp [remove,coord]; grind
       simp only [hj]
       simp [hm,hi,h.ne,remove,coord,diff,menu, Exterior.parity,Exterior.pre];ring -- unfold too early
    rw [←hh F,←hh V,he]
 intro i j x c; unfold menu diff;dsimp only [Pi.sub_apply];rcases lt_trichotomy i j with hk|rfl|hk
 · have H:=hi i j x c hk; unfold diff menu at H;linarith
 rfl
 have H:=hi j i x c hk; unfold diff menu at H;linarith
end YM.RG08.Aura
