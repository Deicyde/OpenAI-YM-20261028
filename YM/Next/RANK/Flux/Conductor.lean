import YM.Next.RANK.Canal
import YM.Next.RANK.Flux.Checkpoint
import YM.Next.RANK.Flux.Chronicle
import YM.Next.RANK.Flux.Routes


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
open Marker Glyph Exponential Finset Lattice Ac Relation Value Corona RG Wilson MeasureTheory Tapes Spindle Atlas Station Peak Cells Perch
open scoped BigOperators Classical

variable {V ι : Type} [Fintype V] [DecidableEq V] {G : Gauge} {c : Family G} {N k m i p a q D : ℕ} {x : Points m} {η y b r z φ : ℝ}
variable {S : Era} {R : Lead G c.S p} {P : Rep G (c.side (i+1) p)} {Q : Rep G (c.side i p)}
variable {h : i+1 ≤ N} {X : Course c N p k}

def rawRadii {n : Side} {Q : Rep G n} {u : V→Site n} (T : Vac u Q) [Fintype ι] (S : ι→Plug G u Q.p.threshold) (v : ι→Prop) (r e M L y z : ℝ) :=
    ∃ f g, Authorship S (measureH T) T.pay f g v (fun _ => r) e M L y z

-- γ and α weights actual
section
variable (i : ℕ)
end

def kinetics (x : ℝ) := Perch.bill (-1/8) x
def firstN (u : ℝ) := Perch.bill (-3) u
-- λ reweight. meter input at λ scale. permits every smaller H if intrinsic tests meet quoted z.
def fareP (S : Era) (φ z u : ℝ) := S.α * z + Perch.bill (-φ) u
def Line (S : Era) (φ z u : ℝ) := max 1 (firstN u / fareP S φ z u)
lemma paid_line (S : Era) (h : 0≤z) : firstN y / Line S φ z y ≤ fareP S φ z y:= by
  have hp : 1≤Line S φ z y:= le_max_left _ _; have he:0<fareP S φ z y:= add_pos_of_nonneg_of_pos (mul_nonneg (zero_le_one.trans S.pay) h) (Real.exp_pos _)
  apply (div_le_iff₀ (zero_lt_one.trans_le hp)).2; rw [mul_comm]; exact (div_le_iff₀ he).1 (le_max_right 1 _)
lemma gas_le (A : Demand) (s : ℝ) : 0 < Perch.gas A s∧Perch.gas A s ≤1:= ⟨Real.exp_pos _,Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr A.posA.le) (sq_nonneg _))⟩

-- Recalled first-system centers on this dictionary, not final logs or correction identities
section
variable {hk : i<k} {hl : middle c.path.levels b k ≤ i}
variable (Y : Ignition R b x X hk hl S.coast.Q a P.p Q.p η) (B : Vac (readers (C:=c) (b:=b) (p:=p) x X.allow (hk.le.trans X.allow)) Q)
-- Kernel first-system oracle. y budget all f/g at that step. *No* panel/log.
structure Audience (Y : Ignition R b x X hk hl S.coast.Q a P.p Q.p η) (B : Vac (readers (C:=c) (b:=b) (p:=p) x X.allow (hk.le.trans X.allow)) Q) (r e : ℝ) : Prop where
  gathered W (hW : principle c P.p X.allow x b (show i+1≤k from hk) S.coast.Q a p W) (hF : Shine W P.p (fun _=>r) (load S) (Perch.bill (-4) (clim c.path.levels k)))
      (ι κ : Type) (_ : Fintype ι) (_ : Fintype κ) (x' : ι→ SourceAt G (readers (C:=c) (b:=b) (p:=p) x X.allow ((show i+1≤k from hk).trans X.allow))) (v : κ → Lifted G (readers (C:=c) (b:=b) (p:=p) x X.allow ((show i+1≤k from hk).trans X.allow)) P.p.threshold) z (hZ : 0 ≤ z) (he : z ≤ Perch.bill (-4) (clim c.path.levels k)) :
    Light P x' v (fun _=>r) (load S) z (Perch.gas S.coast (clim c.path.levels (i+1))) → Background P v →
      ∃ (α : Type), ∃ (_ : Fintype α), ∃ (D : α → Plug G (readers (C:=c) (b:=b) (p:=p) x X.allow (hk.le.trans X.allow)) Q.p.threshold) (s : α → Prop),
        let u:= clim c.path.levels k
        Matric B D ((c.path.levels.clock.op i p).push (X.changeβ (i+1)) (Value.dust P (Sum.elim x' W) v)) ∧
          rawRadii B D s r (load S) ( (Perch.gas S.coast (clim c.path.levels i) ^ 2)⁻¹) (Line S e z u) (kinetics u) (firstN u) ∧
            (∀ i : Bright D, s i.val → Slice (sunny D) i (a/3 * Q.p.B)) ∧
              ∀ (j : Lane c k b p a x hk.le) U hh,
                let T:= litWord p X.allow b c j.1 j.2.val
                bed T.val (pitch (Q:=Q.p) D s U)= bed T.val (insertAt j.1 (planters (Y.tag j U hh) (fun i=> (W (j.1,i)).value)))

-- uses ANY incidence before projector.
lemma taps (hn : m≤2) (ht : Allowed c.path.levels b k) (h : roomTest c.path.levels b k p a S.coast.Q) (hv : Fit c.path.levels b k x) (he : Q.p.B=Perch.walls (clim c.path.levels i))
    (hr : 0<r) (hz : Tickets Q.p (kinetics (clim c.path.levels k))) (hp : Audience Y B r φ) : Pleases S P Q η φ Y r:= by
  constructor; intro W hW hF z hb hB ι κ h₁ h₂ ζ Γ H L hl' hbg
  let F:= (c.path.levels.clock.op i p).push (X.changeβ (i+1)) (Value.dust P (Sum.elim H W) L)
  obtain ⟨α,hα,D,s,hM,hA,hS,hG⟩:= hp.gathered W hW hF ι κ h₁ h₂ H L z hb hB hl' hbg
  let Q₀:=upstairs B D s;let Q₁:=downstairs B D s
  have hc:∀ v : Top B D s,Routes (a*Q.p.B) (Q₀ v) (S.coast.Q*Q.p.B):= fun v=> racks (hk:=hk.le) _ _ _ hS _ v.property he (by linarith only [Nat.mul_le_mul_right Q.p.B (show 3*(a/3) ≤ a by omega)]) h hn hl hv ht
  let K:=after D (measureH B) B.pay
  obtain ⟨hR,hT⟩:=sunny_pass B D F hM s
  let t:=clim c.path.levels i; let u:=clim c.path.levels k; let f:=firstN u; let M:= (Perch.gas S.coast t^2)⁻¹;let w:=Line S φ z u
  have hy:1≤M:= one_le_inv₀ (pow_pos (gas_le _ _).1 _) |>.2 (pow_le_one₀ (gas_le _ _).1.le (gas_le _ _).2)
  obtain ⟨hx,Hx,H'⟩:= authenticity B D s (fun _=>r) (fun _=>hr) hy (show 1 ≤ w from le_max_left ..) (by unfold load; linarith only [S.coast.base]) hz hA
  refine ⟨_,_,_,inferInstance,inferInstance,inferInstance,Q₁,Q₀,K,hT,Shine.loose hx (paid_line S hb),Stripes.loose H' (by simp [M,t]),Shine.loose Hx (Glimmer.billed _ (by norm_num : (-3:ℝ)≤ -2)),hc,hR,fun j U hh=> ?_⟩
  apply sated Q₀ Y j U hh _ hn hc h hv ht he (Eq.trans ?_ (hG j U hh))
  apply congr_arg; exact sunlight B D s U
end

variable (h' : i+1≤ N) (X : Course c N p k)
-- No output W. auth cap can choose $γ=z E$/2 to pay with no partner multiplier. ignores lead current.
structure Dark (x : Points m) (S : Era) (b r : ℝ) (P : Rep G (c.side (i+1) p)) (Q : Rep G (c.side i p)) (B : Vac (readers (C:=c) (b:=b) (p:=p) x X.allow ((Nat.le_succ _).trans h')) Q) : Prop where
  buys (α β : Type) (_ : Fintype α) (_ : Fintype β) (H : α→ SourceAt G (readers (C:=c) (b:=b) (p:=p) x X.allow h')) (K : β → Lifted G (readers (C:=c) (b:=b) (p:=p) x X.allow h') P.p.threshold) z (hZ : 0≤ z) (hz : z ≤ Perch.bill (-1/2) (clim c.path.levels k)) :
    Light P H K (fun _ => r) S.coast.e z (z * w (clim c.path.levels (i+1))) → Background P K → ∃ (ι : Type), ∃ (_ : Fintype ι),∃ (A : ι→ Plug G (readers (C:=c) (b:=b) (p:=p) x X.allow ((Nat.le_succ _).trans h')) Q.p.threshold),
      Matric B A ((c.path.levels.clock.op i p).push (X.changeβ (i+1)) (Value.dust P H K)) ∧
        rawRadii B A (fun _=> False) r S.coast.e (Perch.gas S.coast (clim c.path.levels (i+1)))⁻¹ 1 (kinetics (clim c.path.levels k)) ((S.α*z+Perch.bill (1/2) (clim c.path.levels k)* z^2)/2)
private lemma weaker {n : Side} [Fintype ι] {u : V→Site n} {P : BudgetPoint} (K : ι→Lifted G u P.threshold) {r : V→ℝ} {x e w : ℝ} (h : e≤x) (hr : ∀ i,0< r i) (hp : Stripes P K r x w): Stripes P K r e w:= by
  obtain ⟨p,hP,H⟩:=hp; refine ⟨p,fun i=> ⟨(hP i).1,fun U => ?_⟩,H⟩; apply le_trans _ ((hP i).2 U); gcongr <;> first | exact (Poly.worth hr _).le| unfold Value.charge; gcongr

lemma tapped (B) (he : Tickets Q.p (kinetics (clim c.path.levels k))) (ht : Dark h' X x S b r P Q B) (hr : 0<r) : NonLeading S x r X i P Q b:= by
  constructor; intro i' α β hα hβ ζ ψ H K z hv hx hh hB
  obtain ⟨ι,hι,A,hM,hL⟩:=ht.buys α β hα hβ H K z hv hx hh hB
  let v:=fun _ : ι=> False
  let y:= clim c.path.levels k;let s:= S.coast;let e:=s.e; let u:=Perch.gas s (clim c.path.levels (i+1)); let p':=S.α*z+Perch.bill (1/2) y*z^2
  let D:=downstairs B A v;let J:= upstairs B A v;let K':=after A (measureH B) B.pay
  obtain ⟨a,b,c⟩:= authenticity B A v _ (fun i=>hr) (M:=u⁻¹) ((one_le_inv₀ (gas_le _ _).1).2 (gas_le _ _).2) (L:=1) le_rfl s.base he hL
  obtain ⟨hF,hZ⟩:=sunny_pass B _ _ hM v
  have hq := Shine.plus D J a b
  refine ⟨_,_,inferInstance,inferInstance,Sum.elim D J,K',hF,hZ,Shine.loose hq ?_, Stripes.loose (weaker K' (show e≤e+1 by linarith only) (fun _=>hr) c) ?_ ⟩
  · change p'/2/1+p'/2 ≤ p'; linarith only
  change 1/u⁻¹≤u; simp
end YM.Next.Rank.Flux
