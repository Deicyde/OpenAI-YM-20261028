import YM.Next.RANK.Flux.Conductor
import YM.TraceExtension.Prom.Hill.Allowance
import YM.TraceExtension.Prom.Hill.LedgerGate
import YM.TraceExtension.Prom.Hill.Memorandum
import YM.TraceExtension.Prom.Hill.Station
/-!
  Variant of YM.Next.RANK.Flux.Conductor for dynamic stops. Pulse extension.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Flux
open Marker Glyph Exponential Finset Lattice Ac Relation Value Corona RG Wilson MeasureTheory Tapes Spindle Atlas Station Peak Cells Perch
open scoped BigOperators Classical

variable {V ι : Type} [Fintype V] [DecidableEq V] {G : Gauge} {c : Family G} {N k m i p a q D : ℕ} {x : Points m} {η y b r z φ : ℝ}
variable {S : Era} {R : Lead G c.S p} {P : Rep G (c.side (i+1) p)} {Q : Rep G (c.side i p)}
variable {h : i+1 ≤ N} {X : Course c N p k}

-- γ and α weights actual
section
variable (i : ℕ)
end

-- λ reweight. meter input at λ scale. permits every smaller H if intrinsic tests meet quoted z.

-- Recalled first-system centers on this dictionary, not final logs or correction identities
section
variable {hk : i<k} {hl : middleSky c.path.levels b k ≤ i}
-- Kernel first-system oracle. y budget all f/g at that step. *No* panel/log.

-- uses ANY incidence before projector.

end

variable (h' : i+1≤ N) (X : Course c N p k)
-- No output W. auth cap can choose $γ=z E$/2 to pay with no partner multiplier. ignores lead current.
structure DarkSky (x : Points m) (S : Era) (b r : ℝ) (P : Rep G (c.side (i+1) p)) (Q : Rep G (c.side i p)) (B : Vac (readersSky (C:=c) (b:=b) (p:=p) x X.allow ((Nat.le_succ _).trans h')) Q) : Prop where
  buys (α β : Type) (_ : Fintype α) (_ : Fintype β) (H : α→ SourceAt G (readersSky (C:=c) (b:=b) (p:=p) x X.allow h')) (K : β → Lifted G (readersSky (C:=c) (b:=b) (p:=p) x X.allow h') P.p.threshold) z (hZ : 0≤ z) (hz : z ≤ Perch.bill (-1/2) (clim c.path.levels k)) :
    Light P H K (fun _ => r) S.coast.e z (z * w (clim c.path.levels (i+1))) → Background P K → ∃ (ι : Type), ∃ (_ : Fintype ι),∃ (A : ι→ Plug G (readersSky (C:=c) (b:=b) (p:=p) x X.allow ((Nat.le_succ _).trans h')) Q.p.threshold),
      Matric B A ((c.path.levels.clock.op i p).push (X.changeβ (i+1)) (Value.dust P H K)) ∧
        rawRadii B A (fun _=> False) r S.coast.e (Perch.gas S.coast (clim c.path.levels (i+1)))⁻¹ 1 (kinetics (clim c.path.levels k)) ((S.α*z+Perch.bill (1/2) (clim c.path.levels k)* z^2)/2)
private lemma weakerSky {n : Side} [Fintype ι] {u : V→Site n} {P : BudgetPoint} (K : ι→Lifted G u P.threshold) {r : V→ℝ} {x e w : ℝ} (h : e≤x) (hr : ∀ i,0< r i) (hp : Stripes P K r x w): Stripes P K r e w:= by
  obtain ⟨p,hP,H⟩:=hp; refine ⟨p,fun i=> ⟨(hP i).1,fun U => ?_⟩,H⟩; apply le_trans _ ((hP i).2 U); gcongr <;> first | exact (Poly.worth hr _).le| unfold Value.charge; gcongr

lemma tappedSky (B) (he : Tickets Q.p (kinetics (clim c.path.levels k))) (ht : DarkSky h' X x S b r P Q B) (hr : 0<r) : NonLeadingSky S x r X i P Q b:= by
  constructor; intro i' α β hα hβ ζ ψ H K z hv hx hh hB
  obtain ⟨ι,hι,A,hM,hL⟩:=ht.buys α β hα hβ H K z hv hx hh hB
  let v:=fun _ : ι=> False
  let y:= clim c.path.levels k;let s:= S.coast;let e:=s.e; let u:=Perch.gas s (clim c.path.levels (i+1)); let p':=S.α*z+Perch.bill (1/2) y*z^2
  let D:=downstairs B A v;let J:= upstairs B A v;let K':=after A (measureH B) B.pay
  obtain ⟨a,b,c⟩:= authenticity B A v _ (fun i=>hr) (M:=u⁻¹) ((one_le_inv₀ (gas_le _ _).1).2 (gas_le _ _).2) (L:=1) le_rfl s.base he hL
  obtain ⟨hF,hZ⟩:=sunny_pass B _ _ hM v
  have hq := Shine.plus D J a b
  refine ⟨_,_,inferInstance,inferInstance,Sum.elim D J,K',hF,hZ,Shine.loose hq ?_, Stripes.loose (weakerSky K' (show e≤e+1 by linarith only) (fun _=>hr) c) ?_ ⟩
  · change p'/2/1+p'/2 ≤ p'; linarith only
  change 1/u⁻¹≤u; simp
end YM.Next.Rank.Flux
