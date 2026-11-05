import YM.RG08.Ducat.Nickel

/-! # Strict correction after center measurement reset. -/
noncomputable section
namespace YM.RG08.Ducat
open Filter Function Lattice Laurent Pert.Bulk Forms Room Carrel Steam Isles Rows Rate Stair RG Stationary Bloch Rudder RG08.Mount Tack Anchor Spar Sedan Precision Finset Exterior Nacre PowerSeries Finset.Nat
open scoped Classical BigOperators PowerSeries Topology
set_option autoImplicit false
variable {G:Gauge}(hg:G.Simple){O:Type}{D:Exchange O}{d:O→ℝ}{r e:ℕ}

def victim (A:Castle G)(r e:ℕ):Gird G r:= A r e - if hr:r=0 then torque A hg e • (hr ▸ A 0 0) else 0

def snap (A:Castle G)(e r:ℕ):Gird G r:=∑ i∈ (range e).erase 0,dues (torque A hg) i (RG08.Mount.rank r) e • victim hg A r i
lemma ident (A:Castle G)(hw:Loop.Core (A 0 0) (1/2))(hA:Fair A)(he:0<e): Nacre.send A hg r e=victim hg A r e+snap hg A e r:=by
 let n:=RG08.Mount.rank r
 unfold send Nacre.size
 let w:=torque A hg
 change (∑ i∈Nacre.square e,dues w i n e • A r i)=_
 have hx:= reset w (show w 0=1 by unfold w torque Loop.reading;rw [Loop.measured _ hg hw];norm_num) (le_refl e)
 have hz : (∑ i∈Nacre.square e,dues w i n e • victim hg A r i)= victim hg A r e+snap hg A e r:=by
    have hy: victim hg A r 0=0:=by
       unfold victim;split
       next hr=> subst r;change _-torque A hg 0 • _=0
                 rw [torque,Loop.reading,Loop.measured _ hg hw];norm_num
       next hr=> rw [sub_zero,hA.rests r 0 (by unfold Live;omega)]
    rw [Nacre.square, Finset.sum_range_succ,← Finset.sum_erase_add _ _ (show 0∈ range e by simpa only [mem_range] using he), hy,smul_zero,due_self,one_smul];unfold snap;rw [add_zero,add_comm] -- due_self
 rw [←hz]
 unfold victim
 by_cases h:r=0
 swap
 · simp only [dif_neg h,sub_zero]
 subst r
 simp only [↓reduceDIte,smul_sub,smul_smul,sum_sub_distrib,←sum_smul]
 rw [if_neg (by omega)] at hx
 change _= _ - (∑ i∈range (e+1),dues w i 2 e * w i) • (A 0 0);rw [hx,zero_smul,sub_zero]

lemma Lance.twist {w:O→ℝ}{n:ℕ}{f g:O→ℝ}{I:O→Type}{A B:∀ i:O,Flake n (Market (I i))}(he:Weigh D d f g)(h:Lance D w d A B)(hd:∀ i,0 ≤ d i): Lance D w d (fun i=>f i • A i) (fun i=>g i • B i):=by
 obtain ⟨p,hp,h⟩:=h
 obtain ⟨q,hq,he⟩:=he
 exact ⟨_,D.moreover _ _ (D.steady _ zero_le_two) (D.moreover _ _ hq hp),fun i=>(h i).shift (he i).2.2 (he i).1 (he i).2.1 (hd i)⟩

variable {A B: O→ Castle G}{w:ℕ→ℕ→O→ℝ}
private lemma meter {X Y:O→ Sedan.Wheel G}{v:O→ℝ}(hv:∀ i,0<v i)(hd:∀ i,0≤ d i)(h:Ducat.Mount (r:=0) D v d X Y): Weigh D d (fun i=>Loop.measure (X i) hg/(1/2)) (fun i=> Loop.measure (Y i) hg/(1/2)):=by
 obtain ⟨p,hp,h⟩:=h
 refine ⟨_,D.moreover _ _ hp (D.steady 2 zero_le_two),?_⟩
 intro i;obtain ⟨hx,hy,hk,hS⟩:=h i
 have he:0≤v i:=(hv i).le
 change |Loop.measure (X i) hg / _| ≤ p i * _ ∧ _;rw [←sub_div,abs_div,abs_div,abs_div];norm_num
 obtain ⟨t,u⟩:|Loop.measure (X i) hg| ≤ p i ∧ |Loop.measure (Y i) hg| ≤ p i:=⟨Loop.bill_meter hg hx he hy,Loop.bill_meter hg hx he hk⟩
 rw [←Loop.var_meter hg hx hx he hy hk];have hT:=Loop.bill_meter hg (mul_nonneg hx (hd i)) he hS
 -- norm_num? inspect
 refine ⟨by linarith,by linarith,by rw [abs_div];norm_num;nlinarith⟩

-- neighboring reset, preceding terms only, output widths monotonic
lemma offer (hA:Book D A B w d e r)(ha:∀ i,Fair (A i))(hb:∀ i,Fair (B i))(hw:∀ i r x,0<w i r x)(hd:∀ i,0≤d i)(hz:∀ i p : ℕ, i<e → p ≤ i→∀ x,w e r x ≤ w i p x): Ducat.Mount (r:=r) D (w e r) d (fun i=>snap hg (A i) e r) (fun i=>snap hg (B i) e r):=by
 have hr {i p:ℕ}(hi:i<e):Ducat.Mount (r:=p) D (w e r) d (fun x=>A x p i) (fun x=>B x p i):=by
    by_cases h:RG08.Mount.Live p i
    · exact (Lance.vow (I:=Gear O G) (hA i p ⟨h,Or.inl hi⟩) (fun _=>le_rfl) (hz _ _ hi h.1))
    simp_rw [fun i=> (ha i).rests _ _ h,fun i=> (hb i).rests _ _ h];exact Ducat.zero D _ _
 have hW {i:ℕ}(hp:i<e):Weigh D d (fun x=>torque (A x) hg i) (fun x=>torque (B x) hg i):=meter hg (hw _ _) hd (hr hp)
 apply Lance.series _ _ _ _ hd;intro i hi
 obtain ⟨hq,hN⟩:=mem_erase.mp hi; have ht:=mem_range.mp hN
 apply Lance.twist (sizes hd e i (RG08.Mount.rank r) (fun n hn _=>hW (by omega:n<e))) _ hd
 by_cases he:r=0;swap
 · simp only [victim,dif_neg he,sub_zero];exact hr ht
 subst r
 have hx:Ducat.Mount (r:=0) D (w e 0) d (fun x=>torque (A x) hg i • (A x 0 0)) (fun x=>torque (B x) hg i • (B x 0 0)):=Lance.twist (I:=Gear O G) (hW ht) (hr (by omega:0<e)) hd
 change Lance _ _ _ (fun x=>_ - torque (A x) hg i • _) (fun x=>_- torque (B x) hg i • _);apply Lance.sub (I:=Gear O G) (hr ht) hx hd
end YM.RG08.Ducat
