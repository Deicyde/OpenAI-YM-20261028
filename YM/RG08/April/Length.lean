import YM.RG08.April.Caps
/-! # Inverse formal alphabet profiles post. After step variety. No assertion about diagonal
bare-coupling threshold. -/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.April
open Lattice Laurent Pert.Bulk Forms Room Carrel Steam Isles Rows Rate Rate.Stair RG Stationary Bloch Rudder RG08.Mount Tack Anchor Spar Sedan Precision Finset Exterior Nacre PowerSeries Finset.Nat Symmetry Prism Quarry Roost Packets Ducat Mason
open Function Jetty Precision Skiff Weald Hatch Planned.PrimaryIntegral295 Labels Source Source.Drops WardBin Parts Atrium Trill Necks Sideshow MeasureTheory
open scoped Classical Matrix BigOperators PowerSeries Topology ENNReal
variable {X Z:Type}{G:Gauge}{D d p l e n k r:ℕ}(F:Labels.Frame G d)
local notation "Δ"=> stance (Loc G 1)
local notation "I₀"=> Accent F
local notation "M₀"=> Playbook F
lemma shackles (M N: X→Playbook F)(h:Ducat.Exchange X)(k:ℕ)(he:∀ i≤k,∀ j v,Oil h (fun x=>dusk i (M x) j v) (fun x=>dusk i (N x) j v)):∃ p q:X→ℝ,h.Good p∧(∀ i,1≤ p i)∧h.cheap q∧∀ i≤k,∀ x,
 Atrium.post (dusk i (M x)) (p x) ∧ Atrium.post (dusk i (N x)) (p x) ∧ Atrium.post (dusk i (N x-M x)) (p x*q x):=by
 let I:=I₀×I₀×Fin (k+1)
 obtain ⟨a,b,ha,hb,h₁⟩:= farmOil (fun (t:I)=> he t.2.2.val (by omega) t.1 t.2.1)
 let p(i:X):=1+a i
 have hp(i):1 ≤ p i:=le_add_of_nonneg_right (h.safe _ ha _)
 refine ⟨p,b,h.hear _ _ (h.steady _ zero_le_one) ha,hp,hb,fun i hi x=>?_⟩
 have h₂(j v:I₀):=h₁ (j,v, (⟨i,Nat.lt_succ_of_le hi⟩:Fin (k+1))) x
 refine ⟨fun j v=> (h₂ j v).1.trans (le_add_of_nonneg_left zero_le_one),fun j v=>(h₂ j v).2.1.trans (le_add_of_nonneg_left zero_le_one),fun j v=>?_⟩
 rw [dusk_diff,Matrix.sub_apply,abs_sub_comm];exact (h₂ j v).2.2.trans (le_mul_of_one_le_left (tiny _ hb _) (hp _))
lemma awake_dial (W:Rate.Stair X)(T:Dials G W D d k)(A:Hol G)(Y Y':Boundary F W D k T.filter T.paid)(hm:Paid F T A)(i:Mason.Run W):∃ C:ℝ,1≤C ∧
   Monogram F (T.P i).L C ((T.plot F W A Y Y' hm).P i)∧ Monogram F (T.P i).L C ((T.plot F W A Y Y' hm).P' i):=by
 obtain ⟨C,hc,hs⟩:= awake F _ _ _ _ A T.κ _ _ _ _ _ (T.fee i)
 obtain ⟨h,h'⟩:=T.shoot_valid F W A Y Y' (past W i)
 exact ⟨C,hc,hs (T.foil i (T.score i) le_rfl) (T.warm i) h.unbound h'.unbound h.seats h'.seats h.merit h'.merit⟩
/-- One-step inverse all-order through k, difference local g convention by Oil theorem.
 No nonperturbative readout claims and no conclusion on compatibility with changed $	au$. -/
theorem sighter (W:Rate.Stair X)(T:Dials G W D d k)(A:Hol G)(Y Y':Boundary F W D k T.filter T.paid)(he:Paid F T A)(hp:W.Admits):
 let h:=turnstile W;let H:=T.plot F W A Y Y' he; let u(f:Mason.Run W)(i:I₀):=((T.P f).L.val:ℝ)^(d-gamut i)
 ∃ p q:Mason.Run W→ℝ,h.Good p ∧ h.cheap q ∧ ∀ (i:Mason.Run W)(e:ℕ),e≤k → let M:=evacuate (H.P i) (u i);let R:=evacuate (H.P' i) (u i)
   ; Atrium.post (dusk e M) (p i)∧ Atrium.post (dusk e R) (p i) ∧ Atrium.post (dusk e (M-R)) (q i):=by
 intro h H u
 obtain ⟨p,q,h₁,h1,h₂,hP⟩:= shackles F H.P H.P' h k (fun b hb i j=> seraph F W H hp j i hb) -- seraph W explicit?
 obtain ⟨C,hC,h⟩:= evacuate_price F k
 let Ht:= turnstile W -- h shadow
 have hF:Ht.Good fun i=> C (p i):= steadyPay Ht hC h₁ h1
 let f(i:Mason.Run W):=p i+C (p i)
 let s:ℝ:= Fintype.card I₀; let w(i:Mason.Run W):= (((k:ℝ)+1)*s)^2 * (f i)^3*q i
 have hG:Ht.Good f:= Ht.hear _ _ h₁ hF
 refine ⟨f,w,hG,Ht.awe _ _ (Ht.moreover _ _ (Ht.steady _ (sq_nonneg _)) (stairs _ hG _)) h₂,?_⟩
 intro i e he' M R
 obtain ⟨v,_,hv,hv'⟩:= awake_dial F W T A Y Y' he i
 have hm(j)(hj:j≤k):Atrium.post (dusk j M) (C (p i)):=h hv.funded (gauge_scale F (T.P i).L) _ (h1 i) (fun j hi=> (hP j hi i).1) j hj
 have hr(j)(hj:j≤k):Atrium.post (dusk j R) (C (p i)):=h hv'.funded (gauge_scale F (T.P i).L) _ (h1 i) (fun j hi=>(hP j hi i).2.1) j hj
 have he(i):= hC.nn (h1 i)
 have hX:C (p i)≤f i:=le_add_of_nonneg_left (zero_le_one.trans (h1 _))
 have H1:=evacuation (H.score i).1 hv.funded; have H2:=evacuation (H.score i).2 hv'.funded
 have ht:= inkDelta (δ:=q i) H1.right H2.left (W:=f i) (Ht.safe _ hG _) k (N:=M) (S:=R) (fun j hj x y=>(hm j hj x y).trans hX) (fun j hj x y=> (hr j hj x y).trans hX) (fun j hj x y=>?_ ) (tiny Ht h₂ i) e he'
 · exact ⟨fun a b=>(hm e he' a b).trans hX,fun a b=>(hr e he' a b).trans hX,ht⟩
 exact ((hP j hj i).2.2 x y).trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (he i)) (tiny Ht h₂ i))
end YM.RG08.April
