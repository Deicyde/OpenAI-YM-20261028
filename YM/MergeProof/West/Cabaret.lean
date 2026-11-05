import YM.MergeProof.West.Lins
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Curtain



/-!
# Slicing a leading unit

Before Bake/log. Even overlapping raw addresses take in tangential
crest restrictions. Use n≤2 only AFTER proving one copy per Club.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Display
open YM.Next.Rank.Tapes.West
open Function MeasureTheory Lattice Wilson RG Pressure Next.Rank Next.Rank.Perch Tapes
     Spindle Glyph Peak Ac Thirst Corona Value Marker Next.Rank.Station Relation Finset
     Flux
open scoped Topology BigOperators Classical
variable {G : Gauge} {C : Family G} {i k N p n a q : ℕ} {ξ : Purse}
    (s : ℝ) (X : Points n) (hN : k≤N) (hp : i<k)
local notation "X0" => Atlas.clim C.path.levels i
local notation "y" => Atlas.clim C.path.levels (i+1)
local notation "bK" => walls X0
local notation "bF" => walls y
local notation "St" => (C.path.levels.clock.op i p)
set_option quotPrecheck false
local notation "L1" => (Bale C k s p a X (show i+1≤k from hp))
local notation "rd" => (readers (C:=C) (b:=s) (p:=p) X hN ((show i≤k from hp.le).trans hN))
local notation "rf" => (readers (C:=C) (b:=s) (p:=p) X hN ((show i+1≤k from hp).trans hN))
local notation "Mar" => (Ship.yard C s hN p).Cell × Fin n
local notation "prn" => (C.path.levels.clock.op i p).ratio.parent
lemma roi (v : L1) (w : Bale C k s p a X (show i≤k from hp.le)) :
    (litFt p hN s C v.1 v.2.val).val ⊆ (litFt p hN s C w.1 w.2.val).val ↔ v.1=w.1 ∧ Tapes.West.t_ests (C:=C) X s hp w.2.val v.2:= by
  constructor
  · intro H; have hz:(v.1,Head v.2.val)∈(litFt p hN s C w.1 w.2.val).val:= H (mem_product.mpr ⟨mem_singleton_self _,head_member _⟩)
    exact ⟨mem_singleton.mp (mem_product.mp hz).1,fun i hi=> (mem_product.mp (H (show (v.1,i)∈(litFt p hN s C v.1 v.2.val).val from mem_product.mpr ⟨mem_singleton_self _,hi⟩))).2⟩
  rintro ⟨h,h'⟩ ⟨j,w⟩ hh; obtain ⟨hv,hz⟩:= mem_product.mp hh; exact mem_product.mpr ⟨mem_singleton.mpr ((mem_singleton.mp hv).trans h),h' hz⟩

lemma e_gress (hl : middle C.path.levels s k≤ i) (hr : roomTest C.path.levels s k p a q) (j : L1) (Y : Mar) (ht : Y∈(litFt p hN s C j.1 j.2.val).val) :
    wings St bK (d_olm X s q bF hN hp j.1 j.2.val) ⊆ Spindle.patch (3*bK) (rd Y) := by
  rcases j with ⟨i',j⟩; rcases Y with ⟨z,r⟩; obtain ⟨ht,hv⟩:=mem_product.mp ht; replace ht:=mem_singleton.mp ht; change z=i' at ht; subst z
  intro z hz; obtain ⟨u,hu,hz'⟩:= halo_spec.mp hz; obtain ⟨b,hb,rfl⟩:=mem_image.mp hu
  let D:= rd (i',r); let p':=rd (i',Head j.val)
  have he:separation p' (prn b) ≤ bK:= by
    unfold p'; rw [penultimate s X hN hp]; exact spends_aloft _ hr hp hl _ _ (doors _|>.1 hb)
  have hT : separation D p' ≤ bK:= (separation_comm ..).trans_le (le_trans (le_of_eq (Tapes.together (C:=C) X s p hN hp.le ((Station.wider ..).trans hl) i' (Head j.val) r)) (root_b X hr hp hl j _ hv))
  apply (doors _).2; exact ((separation_triangle ..).trans (add_le_add hT ((separation_triangle ..).trans (add_le_add he hz')))).trans (by omega)

variable {τ : ℝ}

-- parameter before wings costs
structure F_ring (L : Lantern G St) (q : ℕ) (H : L1 → Flake St G (retime X0) L.park rd τ) : Prop where
  hull j : (H j).space=wings St bK (d_olm X s q bF hN hp j.1 j.2.val)
  sees j : (H j).notes=litFt p hN s C j.1 j.2.val
section
variable {L : Lantern G (C.path.levels.clock.op i p)} -- H using Q explicit
lemma adm_ft (H : L1 → Flake St G (retime X0) L.park rd τ) (h : F_ring s X hN hp L q H) (z : Bale C k s p a X hp.le)
    (hr : roomTest C.path.levels s k p a q) (hl : middle C.path.levels s k≤ i) (b : Club (flakeTone∘H)) (ht : (fires (flakeTone∘H) b.val).val ⊆ (litFt p hN s C z.1 z.2.val).val) :
    zone (flakeTone∘H) b ⊆ d_olm X s q bK hN hp.le z.1 z.2.val:= by
  intro e he; obtain ⟨w,hw,hW⟩:=mem_biUnion.mp he
  have hz :(litFt p hN s C w.1 w.2.val).val⊆_:= (show (litFt p hN s C w.1 w.2.val).val⊆(fires (flakeTone∘ H) b.val).val from fun i hi=>mem_biUnion.mpr ⟨w,hw, (show _∈(H w).notes.val from (h.sees w).symm ▸ (show _ from hi))⟩)|>.trans ht
  obtain ⟨hx,hz'⟩:= (roi s X hN hp w z).1 hz
  let p':=rd (w.1,Head w.2.val); let Q:=rd (z.1,Head z.2.val)
  change e∈(H w).space at hW; rw [h.hull] at hW
  have he :separation p' e ≤ 3*bK:= (Spindle.doors _).1 (e_gress s X hN hp hl hr w (w.1,Head w.2.val) (mem_product.mpr ⟨mem_singleton_self _,head_member _⟩) hW)
  have hQ :separation Q p' ≤ a*bK:= by
    unfold p'; rw [hx]; exact (Tapes.together X s p hN hp.le ((Station.wider ..).trans hl) z.1 (Head z.2.val) (Head w.2.val)).trans_le (p_rized (C:=C) z.2 _ (hz' (head_member _)))
  exact (Spindle.doors _).mpr ((separation_triangle Q p' e).trans ((add_le_add hQ he).trans (by have he:= Nat.mul_le_mul_right bK hr.radius; rw [add_mul] at he; omega)))

lemma s_ectors (H : L1 → Flake St G (retime X0) L.park rd τ) (hF : F_ring s X hN hp L q H) (hl : middle C.path.levels s k≤ i)
    (hr : roomTest C.path.levels s k p a q) (hg : Fit C.path.levels s k X) (hz : Allowed C.path.levels s k) (hd : (6*n+3) ≤ a/(3+2*n))
    (u : Club (flakeTone ∘ H)) (j : Mar) (hj : j∈ (fires (flakeTone ∘ H) u.val).val) (x' : Site (C.S.side i p)) (hx : x'∈ zone (flakeTone ∘ H) u): separation (rd j) x' ≤ a/(3+2*n) * bK:= by
  let v : Finset L1:= u.val; let K:= zones (flakeTone ∘ H); let Y := (fires (flakeTone∘H) u.val).val
  have H' (j : L1) (z : Mar) (h : z∈(H j).notes.val): K j⊆ Spindle.patch (3*bK) (rd z):= by change (H j).space⊆_; rw [hF.sees] at h; rw [hF.hull]; exact e_gress s X hN hp hl hr j z h
  have ha (u : L1) (l : L1) (z w : Mar) (hi : z∈(H u).notes.val) (hw : w∈(H l).notes.val) (h : (K u∩ K l).Nonempty) : separation (rd z) (rd w) ≤ 6*bK:= by
    obtain ⟨i,h₁⟩:=h; obtain ⟨h₁,h₂⟩:=mem_inter.mp h₁; have he:=H' u z hi h₁; have ht:= H' l w hw h₂
    exact (separation_triangle (rd z) i (rd w)).trans ((add_le_add ((Spindle.doors _).1 he) ((separation_comm ..).trans_le ((Spindle.doors _).1 ht))).trans (by omega))
  have h₀ (z w : Mar) (hv : separation (rd z) (rd w)≤ 6*bK): z.1=w.1:= by
    by_contra h₂
    have he:= hr.radius; have hs : 6≤3*q:=by omega
    have he':3*q*bK< separation (rd z) (rd w):= periods X s p (hN:=hN) hz hg (h:=hp.le) hl z w h₂ (3*q*bK) (hr.apart i hl hp.le)
    exact he'.not_ge (hv.trans (Nat.mul_le_mul_right _ hs))
  obtain ⟨w,hw,h⟩:= mem_biUnion.mp hj; change j∈ (H w).notes.val at h
  have hv l (p' : chain K v w l) : l∈v ∧ ∀ i∈(H l).notes.val,j.1=i.1:= by
    induction p' with
    | refl=> exact ⟨hw,fun k hk=> h₀ _ _ (ha _ _ j k h hk ⟨_,mem_inter.mpr ⟨(H w).placed j h,(H w).placed j h⟩⟩)⟩
    | @tail t l _ hL Hs=>
      obtain ⟨x,hx⟩:= (H t).nontrivial; obtain ⟨-,hR,e,hx',he⟩:=hL
      exact ⟨hR,fun k hk=> (Hs.2 x hx).trans (h₀ _ _ (ha _ _ _ _ hx hk ⟨e,mem_inter.mpr ⟨hx',he⟩⟩))⟩
  have hY:Y.card≤ n:= by
    have he:Y ⊆ {j.1} ×ˢ univ:= by
      intro i hi; obtain ⟨x,hp,hv'⟩:=mem_biUnion.mp hi; exact mem_product.mpr ⟨mem_singleton.mpr ((hv x (u.property.1.2 w hw x hp)).2 i hv').symm,mem_univ _⟩
    exact (card_le_card he).trans (by simp)
  obtain ⟨p,hp,ht⟩:=mem_biUnion.mp hx
  obtain ⟨e,he⟩:= (H p).nontrivial
  have hh : ∀ m,∀ _:chain K v w m, ∀ i∈(H m).notes.val, ReflTransGen (glows rd Y (6*bK)) j i:=by
      intro m l; induction l with
      | refl=> intro i he; exact .single ⟨hj,mem_biUnion.mpr ⟨w,hw,he⟩, ha w w j i h he ⟨_,mem_inter.mpr ⟨(H w).placed j h,(H w).placed j h⟩⟩⟩
      | @tail m t hL hd ih=>
         obtain ⟨h,hQ,y0,hy,hZ⟩:= hd; intro i hi; obtain ⟨e,he⟩:= (H m).nontrivial; exact (ih e he).tail ⟨mem_biUnion.mpr ⟨_,h,he⟩, mem_biUnion.mpr ⟨_,hQ,hi⟩, ha m t _ _ he hi ⟨y0,mem_inter.mpr ⟨hy,hZ⟩⟩⟩
  have hu: separation (rd j) (rd e) ≤ n*(6*bK) := (trek (hh p (u.property.1.2 w hw p hp) _ he)).trans (Nat.mul_le_mul_right _ hY)
  exact (separation_triangle ..).trans ((add_le_add hu ((Spindle.doors _).mp (H' p e he ht))).trans (by linarith only [Nat.mul_le_mul_right bK hd]))
end
end YM.PhysicalNext.InteractingRank.Display
