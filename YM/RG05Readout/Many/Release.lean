import YM.RG05Readout.Many.Carry
/-!
# Release reservations before exact transmission

At m when dropping separations we authorize openings in a Census. For
one Cartesian separated support packet, the license spends an identically
zero child test for each pair of slots that would resurrect. We explicitly
price an output polynomial, and prove it IDENTICALLY ZERO on those pairs,
without deleting K incompatibilities after adjusting a support. That way
Served reuse at the opening stays within the same physical branch. A
second application may retain a richer RAW pattern even on discarded modes
(e.g. for `Salt` at grouped step); the conclusion about the evaluated
polynomial then needs the surviving modes only.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Many
open Function Finset Filter MeasureTheory Set
open Marker MergeProof Accent Lattice RG Wilson Extra Multi
open Push GridApprox.Nil Ac Extra.Trajectories
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {V W I Y : Type*}[DecidableEq V]
variable {B C:Census V} (h:B.choices ⊆ C.choices)
variable {G:Gauge}{n:Side}

include h in
lemma passable : License B C id:= fun _ he=>h (by simpa using he.1) -- h unused declared!

def narrow:= feed (fun _:V=> (1:ℂ)) (passable h)

def wrap (B C : Census V) (p: Poly B): Poly C:= Poly.inject fun x=> if hi:x.val∈B.choices then p.part ⟨x.val,hi⟩ else 0
def route (x:B.Mode): C.Mode:=⟨x.val,h x.property⟩
lemma wrap_right (p:Poly B)(x:B.Mode): (wrap B C p).part (route h x)= p.part x:= by unfold wrap route; apply dif_pos x.property
lemma wrap_off (p:Poly B)(x:C.Mode)(he:x.val∉ B.choices):(wrap B C p).part x=0:=dif_neg he
lemma narrow_right (p:Poly C)(x:B.Mode): (narrow h p).part x=p.part (route h x):=by
    unfold narrow; rw [parts_of_feed,sum_eq_single (route h x)]; rotate_left
    · intro i _ hi; unfold move; split
      next he=> rw [Poly.part_send,if_neg ?_]; exact fun h'=>hi (Subtype.ext (show i.val=x.val from by simpa [Lit.climb] using congr_arg Subtype.val h'.symm))
      next=> rfl
    · simp
    unfold move; split
    next he=> rw [Poly.part_send,if_pos ?_,Finset.prod_const_one,one_mul]; exact Subtype.ext (by simp [Lit.climb,route])
    next he=> exact False.elim (he (by simp [Lit,route]))
lemma narrow_wrap (p:Poly B):narrow h (wrap B C p)=p:=by ext i; rw [narrow_right,wrap_right]

variable {M:ℕ}{d e t:ℝ}{w:V→ℝ}
    {o:V→Site n}{r:Support n}{F:Config G n → Poly B}
include h
lemma wrap_borne (hc:Borne o r F t) : Borne o r (fun U=>wrap B C (F U)) t:=by
    refine ⟨fun U V hh h' => congr_arg _ (hc.home U V hh h'),fun i U=> congr_arg _ (hc.turns i U),fun i=>?_,fun U i hi=>?_⟩
    · by_cases hx : i.val∈B.choices
      · rw [show i=route h ⟨i.val,hx⟩ from rfl]; simp_rw [wrap_right]; exact hc.me _
      simp_rw [wrap_off _ i hx]; exact measurable_const
    · by_cases hx : i.val∈ B.choices
      · exact (wrap_right h _ ⟨i.val,hx⟩).trans (hc.scope U _ hi)
      exact wrap_off _ _ hx
lemma wrap_burn (hp:Burns o r F t):Burns o r (fun U=>wrap B C (F U)) t:=by
    refine ⟨wrap_borne h hp.toBorne,fun U hu=> hp.permits U (fun ht=> hu ?_),fun U=>?_⟩
    · rw [ht]; ext i; by_cases he:i.val∈B.choices
      · rw [show i=route h ⟨i.val,he⟩ from rfl,wrap_right,Poly.part_nil,Poly.part_nil]
      rw [wrap_off _ _ he,Poly.part_nil]
    exact (wrap_right h _ B.quiet).trans (hp.sil U)
lemma wrap_flow {p:Box n}(hp:Flow o p F t):Flow o p (fun U=>wrap B C (F U)) t:=by
    refine ⟨wrap_borne h hp.toBorne,fun U hu=>hp.permits U (fun H=> hu ?_)⟩
    rw [H]; ext i; by_cases he:i.val∈B.choices
    · rw [show i=route h ⟨i.val,he⟩ from rfl,wrap_right,Poly.part_nil,Poly.part_nil]
    rw [wrap_off _ _ he,Poly.part_nil]
lemma wrap_loci {F:I→ Poly B}(hp:Loci w F t) : Loci w (fun U=> wrap B C (F U)) t:=by
    obtain ⟨f,hf,hV,hX⟩:=hp; let g (i:C.Mode):= if ht:i.val∈ B.choices then f ⟨i.val,ht⟩ else 0
    refine ⟨g,fun i=>?_,fun U i=>?_,?_⟩
    · change 0 ≤ g i; unfold g; split; exact hf _; rfl
    · unfold g; split
      next he=> change ‖(wrap B C _).part (route h ⟨i.val,he⟩)‖ ≤ _; rw [wrap_right]; exact hV _ _
      next he=> rw [wrap_off _ _ he,norm_zero]
    apply le_trans _ hX; apply le_of_eq
    let t' := (Finset.univ: Finset B.Mode); let q := t'.image (route h); let z i:= Poly.toll w i * g i; change ∑ i, z i=_; rw [← Finset.sum_subset (Finset.subset_univ q),show q=t'.image (route h) from rfl,sum_image]; rotate_left
    · intro a _ b _ he; exact Subtype.ext (congr_arg (fun i:C.Mode=>i.val) he)
    · intro i _ hi; unfold z g; split
      next ht=> exact False.elim (hi (mem_image_of_mem (route h) (show ⟨i.val,ht⟩∈t' from Finset.mem_univ _)))
      rw [mul_zero]
    unfold wordsPrice; apply Finset.sum_congr rfl; intro i _; unfold z g route; rw [dif_pos i.property]; rfl
lemma wrap_towed {F:I→Y→Poly B}{r:I→Support n}(hp:Towed w r F M d t): Towed w r (fun i U=>wrap B C (F i U)) M d t:=
    let ⟨f,hf,hV,hE⟩:= hp; ⟨f,hf,hV,fun i=> wrap_loci h (hE i)⟩
lemma wrap_rises {p:Poly B}(he:rises p): rises (wrap B C p):=by
    intro i h'; by_cases ht:i.val∈ B.choices
    · exact he ⟨i.val,ht⟩ ((wrap_right h p ⟨i.val,ht⟩) ▸ (show (wrap B C p).part (route h ⟨i.val,ht⟩) ≠ 0 from h')) -- syntax
    exact False.elim (h' (wrap_off p i ht))
variable {R:Rep G n}{H:Support n→ Config G n→Poly B}{K:Box n→ Config G n→ Poly B}
lemma wrap_carton (ht:Carton o H K t) : Carton o (fun i U=>wrap B C (H i U)) (fun i U=>wrap B C (K i U)) t:=by
    exact ⟨fun i=> ⟨wrap_burn h (ht.exp i).1,fun U=> wrap_rises h ((ht.exp i).2 U)⟩,fun i=>⟨wrap_flow h (ht.flag i).1,fun U=>wrap_rises h ((ht.flag i).2 U)⟩⟩
omit h
lemma id_licenses (C:Census V):License C C id:=passable (subset_refl _)
def temperV (B:Census V)(D:Set V) (p:Poly B):= feed (fun i:V=>if i∈D then 0 else 1) (id_licenses B) p
lemma id_feed (a:V→ℂ) (p:Poly B): feed a (id_licenses B) p=YM.Multi.dilation B a p:=by
    change moveL B B id (YM.Multi.dilation B a p)=_
    generalize YM.Multi.dilation B a p=q; rw [← Poly.studs q,map_sum]; refine sum_congr rfl (fun i _=> ?_); rw [moveL_one,move,dif_pos (show Lit B id i.val from (by simp [Lit,Set.injOn_id]))]; congr 1; exact Subtype.ext (Finset.image_id)

lemma temper_part (s:Set V)(p:Poly B)(i:B.Mode):
    (temperV B s p).part i= if Disjoint s (i.val:Set V) then p.part i else 0:=by
    unfold temperV; rw [id_feed,YM.Multi.dilation_part]; split
    next hd=> rw [Finset.prod_eq_one (fun a h=>if_neg (fun hx=>Set.disjoint_left.mp hd hx h)),one_mul]
    next hd=> obtain ⟨v,hv,hV⟩:= Set.not_disjoint_iff.mp hd; rw [Finset.prod_eq_zero (f:=fun i:V=>if i ∈ s then (0:ℂ) else 1) (show v∈ i.val from hV) (if_pos hv),zero_mul]
section
variable [Fintype V]
set_option maxHeartbeats 500000 in
lemma temper_served {κ:V→Box n→ Config G n→ℂ}{Φ:V→ Config G n→ℂ}(D:Set V)
    {X: Config G n→Poly B} (hX:∀ i∈D,Φ i=0∧κ i=0)(hw:∀ i,0<w i)(hc:Served R Φ κ X o w d t):
    Served R Φ κ (fun U=>temperV B D (X U)) o w d t:=by
    let q:V→ℂ:=fun i=>if i∈D then 0 else 1
    have hz(i): w i*‖q i‖ ≤ w i:=by unfold q; split; rw [norm_zero,mul_zero]; exact (hw i).le; next _=> rw [norm_one,mul_one]
    have he:= carry_served (id_licenses B) q (q:=o) (w':=w) rfl hc hz hw hw
    have hP(i U): q i*Φ i U=Φ i U:=by
       unfold q; split
       next h=>simp [(hX i h).1]
       next=>rw [one_mul]
    have hP'(i p U): q i*κ i p U=κ i p U:=by
       unfold q; split
       next h=>simp [(hX i h).2]
       next=>rw [one_mul]
    change Served _ _ _ (fun U=> feed q _ (X U)) _ _ _ _
    simpa only [hP,hP',id_eq,Finset.sum_ite_eq',Finset.mem_univ,if_true] using he
-- Reopening after temper proof choose temper internal Carton in C too to ensure invalid discarded terms stay zero. K values require hX on tested points only.
include h
set_option maxHeartbeats 600000 in
lemma open_served {κ:V→Box n→ Config G n→ℂ}{Φ: V→ Config G n→ℂ}{X:Config G n→Poly B} (D:Set V) (hp:∀ i∈ D,Φ i=0∧κ i=0)(hw:∀ i,0<w i)
    (hc:Served R Φ κ X o w d t)(hh:∀ U i, ¬Disjoint D ((i.val:Set V)) → (X U).part i=0)(hW:∀ i:C.Mode, i.val∉B.choices → ¬Disjoint D (i.val:Set V)):
     Served R Φ κ (fun U=>wrap B C (X U)) o w d t:=by
    obtain ⟨H,K,hZ,hA,hB,hY⟩:=hc
    have hy:=wrap_carton h hZ; have hW':=wrap_towed h hA; have hK:=wrap_towed h hB
    let h' U:=restore R Φ κ (fun i U'=>wrap B C (H i U')) (fun i U'=>wrap B C (K i U')) U
    have hV:Served R Φ κ h' o w d t:=⟨_,_,hy,hW',hK,rfl⟩
    have hT(U): narrow h (h' U)=X U:=by
       rw [hY]; simpa only [narrow,h',id_eq,one_mul,Finset.sum_ite_eq',Finset.mem_univ,if_true,show ∀ p,feed (fun _=>1) (passable h) (wrap B C p)=p from narrow_wrap h] using carry_restore (passable h) (fun _=>1) (Φ:=Φ) (κ:=κ) hy U
    have he (U): temperV C D (h' U) = wrap B C (X U):=by
       ext i; by_cases hs:i.val∈B.choices
       · let w': B.Mode:=⟨i.val,hs⟩; change (temperV C D (h' U)).part (route h w')=(wrap B C (X U)).part (route h w'); rw [temper_part,wrap_right]; split
         next hv=> rw [← narrow_right,hT]
         next hv=> rw [hh U w' (fun he=> hv he)]
       rw [temper_part,if_neg (hW i hs),wrap_off _ i hs]
    exact funext he ▸ temper_served D hp hw hV
end
end YM.RG05Readout.Many
