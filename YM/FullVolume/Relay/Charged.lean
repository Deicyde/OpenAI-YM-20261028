import YM.FullVolume.Relay.Extent
/- Assembly into full analytic hot estimate on the physical Foil with normalization removed. Denominator also. -/
set_option autoImplicit false
noncomputable section
namespace YM.FullVolume.Nectar
open RG Set Finset Filter Ray Function Amp Beam
open scoped Topology BigOperators Classical ENNReal
open MergeProof MergeProof.Accent Marker Push Push.AbsoluteSums Lattice Wilson Ac GridApprox.Nil
open PhysicalNext.Repeat PhysicalNext.Repeat.Luna.Aank Paint Tower Amp Beam MeasureTheory
open PhysicalNext.Repeat.Muse.Veil Orchard
variable {V:Type}[Fintype V][DecidableEq V]{G:Gauge}{n:Side}{B:Marker.Census V}{p:BudgetPoint}
variable (F:sun→ Rep G n){x: V→ Site n}{w:V→ℝ}(hw:∀ i,0<w i)(hP:∀ s,(F s).p=p)
variable (E:sun→ Support n→ Config G n→Poly B)(K:sun→ Box n→ Config G n→ Poly B)(ν:sun→ V→ℂ)
variable {f:sun→ Config G n→ Poly B}{d q v t s p0 P M:ℝ}{Q C u:V→ℝ}
variable (H:Proceeds F x w E K ν p f s t Q C)
-- prove unpack exponent E assembly separately
lemma Mach_merge (o:V→ Support n→ℂ)(u:V→ℂ) : Mach B u + (∑ i: Support n, Mach B (fun j=>o j i))=Mach B (fun j=> u j+∑ i,o j i):=by
   ext i; rcases Nat.lt_trichotomy i.val.card 1 with h|h|h
   · have he:i=B.quiet:=Subtype.ext (card_eq_zero.mp (by omega));rw [he,Poly.part_plus,mute,Poly.part_sum];simp_rw [mute,sum_const_zero,add_zero]
   · obtain ⟨j,hj⟩:=card_eq_one.mp h; have he:i=B.fire j:=Subtype.ext hj;rw [he,Poly.part_plus,Poly.part_sum]; simp_rw [sing]
   rw [Poly.part_plus,Poly.part_sum]; simp_rw [hush _ _ (show 2 ≤ i.val.card by omega),sum_const_zero,add_zero]
include H hw
lemma spectrum_all (h:∀ i,PaidBeam (fun s=>ν s i) (u i)) (ht:∑ i,w i*(u i+Q i) ≤ M): LeafPaid w (FullVolume.Nectar.spectrum E ν) ((M)+s):=by
   have hv: FullVolume.Nectar.spectrum E ν= (fun s:sun=>fun y=> (Mach B (fun i=> singles E ν s i y))+ ∑ i,G1 E s i y):=by
      funext s x
      have hh(i): E s i x= Mach B (fun j=> (E s i x).part (B.fire j))+G1 E s i x:= by
          conv_lhs=> rw [ballots (E s i x), H.realP.permitE s i |>.sil x,map_zero,zero_add]
      unfold FullVolume.Nectar.spectrum; nth_rw 1 [Finset.sum_congr rfl (fun i _=>hh i)]; rw [sum_add_distrib,← add_assoc]; exact congr_arg₂ HAdd.hAdd (Mach_merge (fun i j=>(E s j x).part (B.fire i)) (ν s)) rfl
   rw [hv]; refine LeafPaid.twin (F:=fun s y=> Mach B (fun i=> singles E ν s i y)) (G:=fun s y=>∑ i,G1 E s i y) ?_ (globalHot hw p.exponent_pos.le H.contact)
   apply LeafPaid.higher _ ht; unfold Mach; refine LeafPaid.daisy (w:=w) (F:=fun i s U=> Poly.send (B.fire i) (singles E ν s i U)) univ _ (fun i _=> ?_)
   let z:(i:V)→(t:sun)→ Config G n→ℂ:=fun i s x=>ν s i
   have hi:= Feel.united (f:=z i) (Treasure.foraged (h i)) (globalSingle hw p.exponent_pos.le (F':=E) (S:=id) (H.singleE i))
   have hp:= LeafPaid.mark (B.fire i) _ hi (w:=w); rw [Poly.solo_toll] at hp; exact hp

abbrev baseNo(s:sun)(U:Config G n): ℝ:= (F s).exponent U-(F s).scalar
abbrev film (F:sun→Rep G n)(f:sun→ Config G n→Poly B)(s:sun)(x:Config G n): Poly B:= (Real.exp (-(F s).scalar):ℂ) • f s x
include hP
lemma film_budget (hv:∀ i,PaidBeam (fun s=>ν s i) (u i)) (ht:∑ i,w i*(u i+Q i) ≤ M) (hp:Feel (baseNo F) P)(hK:WindowP (visaK F) Prod.fst p.B p.supportExponent v)(hW:0 ≤ v) : LeafPaid w (film F f) (Real.exp P*(Real.exp (M+s)*allpriceG n (v+t))):=by
   have hT:= H.contact; have h: Pact w Prod.fst K (lively B) p.B p.supportExponent t:= H.bondK
   have hz: Polaris w Prod.fst K p.B p.supportExponent (v+t):=by
        apply Polaris.from_modes hw h; rw [show receive K B.quiet=visaK F from funext fun i=> funext fun j=> funext (H.realP.echoK i j) ]; exact hK
   have hx:= globalK hw K p.exponent_pos.le (add_nonneg hW (h.price hw)) (H.realP.permitK) hz -- hp order
   have hy:= LeafPaid.mixP hw (LeafPaid.pass hw (spectrum_all F hw E K ν H hv ht)) hx
   have hp': Feel (fun i x=>(Real.exp (baseNo F i x):ℂ)) (Real.exp P):= by simp_rw [Complex.ofReal_exp]; exact (Feel.ofs hp).exponent_c

   convert LeafPaid.school hw hy hp' using 1
   funext i x; unfold film; rw [H.ledger]
   unfold oven play; simp only [smul_smul, ← Complex.ofReal_mul,hP,← Real.exp_add]; unfold baseNo FullVolume.Nectar.spectrum; rw [neg_add_eq_sub]
lemma film_quiet {q v}(hp:∀ s,(F s).activities.Valid p q v): ∀ s U, (film F f s U).part B.quiet=((Real.exp (-(F s).scalar)*(F s).eval U :ℝ):ℂ) :=by
    intro s U; unfold film; rw [Poly.part_smul,H.ledger]; let V:= FullVolume.Nectar.spectrum E ν; change (Real.exp _:ℂ) *(play (F s) B (K s) (V s) U).part B.quiet= _
    rw [bronze (F s) B _ _ _ (hP s|>.symm ▸ hp s) (fun i=> H.realP.echoK s i U) (H.realP.quietE s U), Complex.ofReal_mul]
end YM.FullVolume.Nectar
