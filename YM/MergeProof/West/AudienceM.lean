import YM.MergeProof.West.CheckM
import YM.MergeProof.West.FluxM
import YM.Next.RANK.Flux.Conductor




/-!
# Conversion from first-system output to C value-step permissions

All conditional. Strengthen pre-step cost outputs with Log-connection budget
(tests on FIRST-system amplitudes). This can replace `Pleases` and `NonLeading`
when applying the main budget theorem. Does not assert this Plan SUCCEEDS.
Rep's uniformity, support receipts, stencil, tight step parameters required
from E path. API still uses pose as above; actual mixed-history producers see tests.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Flux
open Tapes.West
open Marker Glyph Exponential Finset Lattice Ac Relation Value Corona RG Wilson MeasureTheory Tapes Spindle Atlas Station Peak Cells Perch
open scoped BigOperators Classical

variable {V ι : Type} [Fintype V] [DecidableEq V] {G : Gauge} {c : Family G} {N k m i p a q D : ℕ} {x : Points m} {η y b r z φ : ℝ}
variable {S : Era} {R : Lead G c.S p} {P : Rep G (c.side (i+1) p)} {Q : Rep G (c.side i p)}
variable {h : i+1 ≤ N} {X : Course c N p k}

section
variable {hk : i<k} {hl : middle c.path.levels b k ≤ i}
variable (Y : IgnFt R b x X hk hl S.coast.Q a P.p Q.p η) (B : Vac (readers (C:=c) (b:=b) (p:=p) x X.allow (hk.le.trans X.allow)) Q)
-- Kernel first-system oracle. y budget all f/g at that step. *No* panel/log.
structure AudFt (Y : IgnFt R b x X hk hl S.coast.Q a P.p Q.p η) (B : Vac (readers (C:=c) (b:=b) (p:=p) x X.allow (hk.le.trans X.allow)) Q) (r e : ℝ) : Prop where
  gathered W (hW : princFt c P.p X.allow x b (show i+1≤k from hk) S.coast.Q a p W) (hF : Shine W P.p (fun _=>r) (load S) (Perch.bill (-4) (clim c.path.levels k)))
      (ι κ : Type) (_ : Fintype ι) (_ : Fintype κ) (x' : ι→ SourceAt G (readers (C:=c) (b:=b) (p:=p) x X.allow ((show i+1≤k from hk).trans X.allow))) (v : κ → Lifted G (readers (C:=c) (b:=b) (p:=p) x X.allow ((show i+1≤k from hk).trans X.allow)) P.p.threshold) z (hZ : 0 ≤ z) (he : z ≤ Perch.bill (-4) (clim c.path.levels k)) :
    Light P x' v (fun _=>r) (load S) z (Perch.gas S.coast (clim c.path.levels (i+1))) → Background P v →
      ∃ (α : Type), ∃ (_ : Fintype α), ∃ (D : α → Plug G (readers (C:=c) (b:=b) (p:=p) x X.allow (hk.le.trans X.allow)) Q.p.threshold) (s : α → Prop),
        let u:= clim c.path.levels k
        Matric B D ((c.path.levels.clock.op i p).push (X.changeβ (i+1)) (Value.dust P (Sum.elim x' W) v)) ∧
          rawRadii B D s r (load S) ( (Perch.gas S.coast (clim c.path.levels i) ^ 2)⁻¹) (Line S e z u) (kinetics u) (firstN u) ∧
            (∀ i : Bright D, s i.val → Slice (sunny D) i (a/(3+2*m) * Q.p.B)) ∧
              ∀ (j : Bale c k b p a x hk.le) U hh,
                let T:= litFt p X.allow b c j.1 j.2.val
                bed T.val (pitch (Q:=Q.p) D s U)= bed T.val (insertAt j.1 (planterFt (Y.tag j U hh) (fun i=> (W (j.1,i)).value)))

-- uses ANY incidence before projector.
lemma tapsFt (ht : Allowed c.path.levels b k) (h : roomTest c.path.levels b k p a S.coast.Q) (hv : Fit c.path.levels b k x) (he : Q.p.B=Perch.walls (clim c.path.levels i))
    (hr : 0<r) (hz : Tickets Q.p (kinetics (clim c.path.levels k))) (hp : AudFt Y B r φ) : PleaFt S P Q η φ Y r:= by
  constructor; intro W hW hF z hb hB ι κ h₁ h₂ ζ Γ H L hl' hbg
  let F:= (c.path.levels.clock.op i p).push (X.changeβ (i+1)) (Value.dust P (Sum.elim H W) L)
  obtain ⟨α,hα,D,s,hM,hA,hS,hG⟩:= hp.gathered W hW hF ι κ h₁ h₂ H L z hb hB hl' hbg
  let Q₀:=upstairs B D s;let Q₁:=downstairs B D s
  have hc:∀ v : Top B D s,Carport (a*Q.p.B) (Q₀ v) (S.coast.Q*Q.p.B):= fun v=> r_acks (hk:=hk.le) _ _ _ hS _ v.property he (by rw [← mul_assoc]; gcongr; exact Nat.mul_div_le a _) h hl hv ht
  let K:=after D (measureH B) B.pay
  obtain ⟨hR,hT⟩:=sunny_pass B D F hM s
  let t:=clim c.path.levels i; let u:=clim c.path.levels k; let f:=firstN u; let M:= (Perch.gas S.coast t^2)⁻¹;let w:=Line S φ z u
  have hy:1≤M:= one_le_inv₀ (pow_pos (gas_le _ _).1 _) |>.2 (pow_le_one₀ (gas_le _ _).1.le (gas_le _ _).2)
  obtain ⟨hx,Hx,H'⟩:= authenticity B D s (fun _=>r) (fun _=>hr) hy (show 1 ≤ w from le_max_left ..) (by unfold load; linarith only [S.coast.base]) hz hA
  refine ⟨_,_,_,inferInstance,inferInstance,inferInstance,Q₁,Q₀,K,hT,Shine.loose hx (paid_line S hb),Stripes.loose H' (by simp [M,t]),Shine.loose Hx (Glimmer.billed _ (by norm_num : (-3:ℝ)≤ -2)),hc,hR,fun j U hh=> ?_⟩
  apply s_ated Q₀ Y j U hh _ hc h hv ht he (Eq.trans ?_ (hG j U hh))
  apply congr_arg; exact sunlight B D s U
end

end YM.Next.Rank.Flux