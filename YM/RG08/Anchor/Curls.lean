import YM.RG08.Anchor.Packed

noncomputable section
namespace YM.RG08.Anchor
open Forms Rudder Packets Isles Finset Function Lattice Laurent Pert.Bulk Exterior Filter Bloch
open AnalyticNext.QuarticMatch.BoxChain hiding sway
open scoped Topology BigOperators Classical ENNReal
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
local notation "Box"=> YM.AnalyticNext.QuarticMatch.BoxChain.Cell
variable {I : Type}{n k:ℕ}{P:Side}
abbrev Sampler (k:ℕ)(P:Side):=Body k P → ℝ

def actual (f:Sampler k P):Postel P:= fun z=> if h:z.2.card=k then f (z.1,⟨z.2,h⟩) else 0
lemma actual_read (f:Sampler k P)(x:Body k P):actual f (x.1,x.2.val)=f x:=by unfold actual;rw [dif_pos x.2.property]
lemma actual_climb(f:Sampler k P): margin (actual f)=actual (((cobound k).acts P).mulVec f):=by
 funext z;by_cases hz:z.2.card=k+1
 · let x:Body (k+1) P:=(z.1,⟨z.2,hz⟩)
   change _=actual _ (x.1,x.2.val);rw [actual_read,discrete,margin,Finset.sum_apply];apply sum_congr rfl;intro i _
   unfold finger;split_ifs with he
   · have hh:(z.2.erase i).card=k:=by rw [card_erase_of_mem he,hz]; rfl -- k+1-1
     rw [actual,actual,dif_pos hh,dif_pos hh];rfl
   · rfl
 rw [actual,dif_neg hz,margin,Finset.sum_apply];apply sum_eq_zero;intro i _
 unfold finger;split_ifs with he
 · have h:(z.2.erase i).card≠k:=by rw [card_erase_of_mem he]; have :=Finset.card_pos (s:=z.2) |>.mpr ⟨i,he⟩;omega
   rw [actual,actual,dif_neg h,dif_neg h,sub_self,mul_zero]
 rfl

private def thin (x:Body k P):Box (Per P):=(x.1,x.2.val)
private lemma thin_injective:Injective (@thin k P):=by rintro ⟨x,i⟩ ⟨y,j⟩ h; simp only [thin,Prod.mk.injEq,Subtype.coe_inj] at h ⊢;exact h

lemma distance (A:ArrayC (Fin n) (Per P) ℝ)(f:Tape n (Sampler k P)):
 stroke A (actual ∘ f)=∑ x:Tape n (Body k P), A (thin ∘ x)*∏ i,f i (x i):=by
 let L: Tape n (Body k P)→ Tape n (Box (Per P)):=fun x=>thin ∘ x
 let U(x:Tape n (Box (Per P))):=A x*∏ i,actual (f i) (x i)
 change (∑ x,U x)=_
 rw [←Finset.sum_subset (f:=U) (s₁:=(univ.image L)) (by simp) ?_,Finset.sum_image (show Injective L from (@thin_injective k P).comp_left).injOn] -- InjOn signature
 · apply sum_congr rfl;intro x _; unfold U L; simp_rw [comp_apply];congr 1;apply prod_congr rfl;intro i _;exact actual_read ..
 intro x _ hx
 have he:∃ i:Fin n,(x i).2.card ≠ k:=by
    by_contra! H
    let a:Tape n (Body k P):=fun i=>((x i).1,⟨(x i).2,H i⟩)
    exact hx (mem_image.mpr ⟨a,mem_univ a,rfl⟩)
 obtain ⟨i,hi⟩:=he
 unfold U;rw [Finset.prod_eq_zero (mem_univ i) (show actual (f i) (x i)=0 from dif_neg hi),mul_zero]

lemma compress_period (F:Flake n (Market (Tone I)))(i:Fin n)(k:ℕ)(x:Tape n (Cove P (Kind I k))):
 pour (compress k F) i x=pour F i (et x):=by
 rw [pour_at,pour_at]
 let u:↥(lantern i x)→↥(lantern i (et x)):=fun t=>⟨et t.val,⟨congr_arg ec ((Set.mem_setOf.mp t.property).1), congr_arg et ((Set.mem_setOf.mp t.property).2)⟩⟩
 have hu:Bijective u:=by
    refine ⟨fun a b h=>Subtype.ext (et_injective (congr_arg (fun v=>v.val) h)),?_⟩
    intro z
    have h(i):(z.val i).2.1.card=k:=by -- syntax
       have he:=congr_arg (fun w=>w.2.1) (Isles.found z.property i)
       change (z.val i).2.1=(x i).2.1.val at he;rw [he,(x i).2.1.property]
    let t:Tape n (Market (Kind I k)):=fun i=>decoded Cover I k (z.val i) (h i)
    have ht:et t=z.val:=rfl
    have hs: t∈ lantern i x:=by
       constructor
       · apply ec_injective; exact (Set.mem_setOf.mp z.property).1
       apply et_injective; exact (Set.mem_setOf.mp z.property).2
    exact ⟨⟨_,hs⟩,Subtype.ext ht⟩
 rw [← Equiv.tsum_eq (Equiv.ofBijective u hu)];rfl

theorem compact_curls {σ C:ℝ}{F:Raw I n}(i:Fin n)(h:NextTo F σ C)(y:Tape n I)(f:Tape n (Sampler 1 P)):
  (∑ x:Tape n (Body 1 P),pour (compress 1 (picture I n F)) i (fun j=>((x j).1,(x j).2,y j))* ∏ j,f j (x j)) =
      ∑ x:Tape n (Body 2 P),pour (compress 2 F) i (fun j=>((x j).1,(x j).2,y j))*∏ j,((cobound 1).acts P).mulVec (f j) (x j):=by
 simp_rw [compress_period]
 have he:=curl_pour i h y (actual ∘ f)
 convert he using 1
 · rw [distance];rfl
 simp_rw [comp_apply,actual_climb] at *
 change _=stroke _ (actual ∘ fun j=>((cobound 1).acts P).mulVec (f j));rw [distance];rfl
end YM.RG08.Anchor
