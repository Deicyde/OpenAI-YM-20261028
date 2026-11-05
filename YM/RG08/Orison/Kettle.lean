import YM.RG08.Orison.Hotel

/-! # Total conditional unfolding under analytic currents -/
noncomputable section
namespace YM.RG08.Orison
open Filter Function Lattice Laurent Pert.Bulk Forms Packets Carrel Steam Rate Stair RG Stationary Bloch Rudder RG08.Mount Tack Anchor Spar Sedan Precision Finset Exterior Nacre PowerSeries Finset.Nat Symmetry Prism Quarry Roost Ducat Mason Yamen Rows
open scoped Classical Matrix BigOperators PowerSeries Topology ENNReal
set_option autoImplicit false
variable {I J:Type} {G:Gauge}{E:ℕ}{V:ℕ→Grain (Market I)}{F:Grain (Market I)}{m:ℕ→Kernel I J}{M:Kernel I J}{g:ℕ→Kernel I I}{T:Kernel I I}

lemma gather {L:Type}(s:Finset L)(P:L→(ℕ→ℝ)→ℝ→Prop)(h:∀ i∈s,∃ d w,hush.cheap d∧0<w∧ P i d w)(hm:∀ i∈s,∀ d d' x x',P i d x→ (∀ i,d i ≤ d' i) → x' ≤ x→ P i d' x'):
 ∃ d w,hush.cheap d ∧ 0<w ∧ ∀ i∈s,P i d w:=by
 induction s using Finset.induction_on with
 | empty=>exact ⟨_,1,hush.zero,zero_lt_one,by simp⟩
 | insert a s ha hi=>
   obtain ⟨d,w,hd,hW,H⟩:=hi (fun i ht=>h i (mem_insert_of_mem ht)) (fun i ht=>hm i (mem_insert_of_mem ht))
   obtain ⟨p,q,hp,hq,hP⟩:=h a (mem_insert_self ..)
   refine ⟨fun i=>p i+d i,min q w,hush.lasts _ _ hp hd,lt_min hq hW,fun i ht=>?_⟩; have hh:=hm i ht; rcases mem_insert.mp ht with rfl|ht
   · exact hh _ _ _ _ hP (fun i=>le_add_of_nonneg_right (tiny _ hd i)) (min_le_left ..)
   exact hh _ _ _ _ (H _ ht) (fun i=>le_add_of_nonneg_left (tiny _ hp i)) (min_le_right ..)

variable [Fintype I][Fintype J]
lemma metro {w w':ℝ}{d d':ℕ→ℝ}(h:Counter (D:=hush) (fun _=>I) (fun _=>J) (fun _=>w) d m (fun _=> M))(hh:w' ≤ w)(hd:∀ i,d i ≤ d' i):Counter (D:=hush) (fun _=>I) (fun _=>J) (fun _=>w') d' m (fun _=> M):=by
 obtain ⟨⟨b,hb,H⟩,hc⟩:=h; refine ⟨⟨_,hb,fun i=>?_⟩,hc⟩;obtain ⟨he,hG,hI⟩:=H i;exact ⟨he.mono hh le_rfl,hG.mono hh le_rfl,hI.mono hh (mul_le_mul_of_nonneg_left (hd i) (hush.safe _ hb i))⟩

section
lemma stands {u v:ℝ}(hV:∀ i,Eligible (V i))(hF:Eligible F)(hp:∀ i k:ℕ,i ≤ E→ k ≤ i+2→0<k→Studio (fun n=>V n i k) (F i k))(ht:Alpine g T u)(hE:Alpine m M v)(hu:0<u)(hv:0<v)(k:ℕ)(hk:k ≤ E+2)(he:0<k):Studio (fun i=>Steam.allG (g i) (V i) (m i) E k) (Steam.allG T F M E k):=by
 let s:Finset (ℕ×ℕ):=((Nacre.square E ×ˢ Nacre.square (E+2))).filter (fun i=> i.2 ≤ i.1+2 ∧ 0 < i.2)
 let p (i:ℕ×ℕ)(d:ℕ→ℝ)(xw:ℝ):= Lance (I:=fun _=>I) hush (fun _=>xw) d (fun n=>V n i.1 i.2) fun _=>F i.1 i.2
 obtain ⟨d,x,hd,hX,H⟩:= Orison.gather s p (fun i hi=> by
    obtain ⟨p,hp,h⟩:=hp i.1 i.2 (Nacre.in_square _ _|>.mp (mem_product.mp (mem_filter.mp hi).1).1) (mem_filter.mp hi).2.1 (mem_filter.mp hi).2.2
    exact ⟨h.choose,p,h.choose_spec.1,hp,h.choose_spec.2⟩) (fun i _ _ _ _ _ he ha hb=> Lance.vow he ha (fun _=>hb))
 obtain ⟨f,h0,hΓ⟩:=ht;obtain ⟨q,hq,hm⟩:=hE
 let r (i:ℕ):= f i+q i+d i; let y:=min x (min u v)
 have hT:hush.cheap r:=hush.lasts _ _ (hush.lasts _ _ h0 hq) hd;have hy:0<y:=lt_min hX (lt_min hu hv)
 have ht(i):= tiny _ hd i;have hf(i):=tiny _ h0 i;have hg(i):=tiny _ hq i
 have hΓ':=metro (w':=y) (d':=r) hΓ ((min_le_right ..).trans (min_le_left ..)) (fun i=>by unfold r;linarith [ht i,hg i])
 have hM':=metro (w':=y) (d':=r) hm ((min_le_right ..).trans (min_le_right ..)) (fun i=>by unfold r;linarith [ht i,hf i])
 have hs (i)(hi:i∈s):p i r y:= Lance.vow (H _ hi) (fun i=>by unfold r; linarith [hf i,hg i]) (fun _=>min_le_left ..)
 have hh0 {i j:ℕ}(h0:i ≤ E)(h1:j ≤ i+2)(h2:0<j):p (i,j) r y:=hs _ (by simp only [s,mem_filter,mem_product,Nacre.in_square];exact ⟨⟨h0,by omega⟩,⟨h1,h2⟩⟩)
 exact ⟨y,hy,r,hT,(Ducat.Lance.reserve (fun _=>hy) (tiny _ hT) (hh0 le_rfl hk he) hM').add (Ducat.receipt_step (fun _=>hy) (tiny _ hT) hM' hΓ' V (fun _=>F) hV (fun _=> hF) E k (fun a p hp=> by unfold Residual taps at hp; exact hh0 (by omega) hp.2.2.1 hp.1) he) (tiny _ hT)⟩
end
lemma conditioned {P:Patch}{Q:KernelChoices}{h:P.Branches Q G}{C:ℕ→Castle G}{D:Castle G}{Z:ChartRatio G}{g:ℕ→Kernel (Tack.Head P G) (Tack.Head P G)}{m:ℕ→Kernel (Tack.Head P G) (Loc G 1)}{u v:ℝ}{G0 :Kernel (Tack.Head P G) (Tack.Head P G)}{M:Kernel (Tack.Head P G) (Loc G 1)}(hg:Alpine g G0 v)(hm:Alpine m M u)(hu:0<u)(hv:0<v)(hH:Shade E C D){e k:ℕ}(he:e ≤ E)(hp:0<k)(hk:k ≤ e+2):
 Studio (fun i=>Steam.allG (g i) (inlet h (C i) Z) (m i) e k) (Steam.allG G0 (inlet h D Z) M e k):= stands (fun i=>inlet_eligible _ _ (hH.paid i).rails) (inlet_eligible _ _ hH.valid.rails) (fun _ _ hi _ hj=>Studio.ghosted hH (hi.trans he) hj) hg hm hv hu k hk hp -- order
end YM.RG08.Orison
