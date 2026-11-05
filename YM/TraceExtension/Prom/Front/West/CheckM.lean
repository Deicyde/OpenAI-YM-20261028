import YM.MergeProof.West.CheckM
import YM.TraceExtension.Prom.Front.West.Flag
import YM.TraceExtension.Prom.Front.West.Mural
import YM.TraceExtension.Prom.Front.West.Throne
import YM.TraceExtension.Prom.Front.West.View
import YM.TraceExtension.Prom.Hill.Allowance
import YM.TraceExtension.Prom.Hill.Camps
import YM.TraceExtension.Prom.Hill.Joints
import YM.TraceExtension.Prom.Hill.Memorandum
import YM.TraceExtension.Prom.Hill.Station
import YM.TraceExtension.Prom.Hill.Tuning
/-!
  Variant of YM.MergeProof.West.CheckM for dynamic stops. Pulse extension.
-/
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.Next.Rank.Flux
open Tapes.West
open Marker Glyph Exponential Finset Lattice Ac Relation Value Corona RG Wilson MeasureTheory Tapes Spindle Atlas Station Peak Cells Perch
open scoped BigOperators Classical

variable {V ι κ α β : Type} {G : Gauge} {n : Side} {c : Family G} {i k N p m a b q : ℕ} {s η : ℝ}

variable {Q : BudgetPoint} {hk : i<k} {x : Points m} {hN : k≤N} {hl : middleSky c.path.levels s k ≤ i} {X : Course c N p k} {R : Lead G c.S p}

variable [Fintype ι] [Fintype κ]
local notation "ζ" => readersSky (C:=c) (b:=s) (p:=p) x X.allow (hk.le.trans X.allow)
variable (S : ι→Plug G ζ Q.threshold) (P : κ → Lining G ζ Q.threshold) (f : ι→Prop)

lemma s_atedSky {P' : BudgetPoint} (B : ι→ SourceAt G ζ) (Y : IgnFtSky R s x X hk hl q b P' Q η) (t : BaleSky c k s p b x hk.le) (U) (hh)
    (u : PatchPt x s c.path.levels p b (show i+1≤k from hk) → Config G (c.side (i+1) p)→ℂ)
    (ht : ∀ v:ι, let W:=B v; Carport (b*Q.B) W (q*Q.B))
    (hr : roomTestSky c.path.levels s k p b q) (hv : FitSky c.path.levels s k x) (ha : AllowedSky c.path.levels s k)
    (hm : Q.B=Perch.walls (clim c.path.levels i))
    -- input correlation BEFORE any marked log
    (Hp : let z:= litFtSky p X.allow s c t.1 t.2.val
          bed z.val (Poly.pass (∑ i,(B i).amount Q.threshold U))= bed z.val (insertAt t.1 (planterFtSky (Y.tag t U hh) u))) :
    let z:= litFtSky p X.allow s c t.1 t.2.val
    let T:= leadFtSky (Y.tag t U hh) u
    ∑ j:ι,(if (B j).fires=z then (B j).value U else 0)= T.part (tag t.2.val).val:= by
  intro z T
  let D := ∑ i,(B i).amount Q.threshold U
  have hq:D.part (quiet _)=0:= by unfold D; rw [Poly.part_sum]; exact sum_eq_zero fun i _=> asleep _ (B i).chosen _
  have hp:Expands D (Poly.pass D):= ⟨hq,rfl⟩
  have he : Expands T (planterFtSky (Y.tag t U hh) u):= connected_spec ..
  have H : Expands (insertAt t.1 T) (insertAt t.1 (planterFtSky (Y.tag t U hh) u)):= by
    refine ⟨(insert_quiet ..).trans he.1,(insert_pass _ _ he.1).trans ?_⟩; exact congr_arg _ he.2
  have hl1 : bed z.val D = bed z.val (insertAt t.1 T):= by
    refine (bedrock z.val hp).uniq ?_
    let d:= bed z.val (Poly.pass D)
    let s0:= insertAt t.1 (planterFtSky (Y.tag t U hh) u)
    have hL : d=bed z.val s0:= Hp
    change Expands _ d
    rw [hL]
    exact bedrock _ H
  have hD : D.part z=T.part (tag t.2.val).val:= by
    rw [← show _=D.part z from (shelve _ _ _).trans (if_pos (subset_refl z.val)),hl1,shelve,if_pos (subset_refl _), insert_part]
    change (if homes {t.1} (Glyph.push t.1 _) then _ else 0)=_; rw [if_pos (settle ..)]; change T.part (fibre _ (Glyph.push t.1 _))=_;rw [dock]
  apply Eq.trans _ hD; unfold D; rw [Poly.part_sum]; apply sum_congr rfl; intro j _; unfold SourceAt.amount; rw [Poly.part_send]; split_ifs with hz h hh'
  · obtain ⟨L,hx,hp⟩:= Tapes.West.f_pairSky (hN:=X.allow) (hk:=hk.le) hl hr hv ha (B j) _ hm (ht j)
    have he := Tapes.West.torchesSky X.allow s p (C:=c) (a₁:=(L.1,L.2.val)) (a₂:=(t.1,t.2.val)) (hx.symm.trans hz)
    have hg : L=t:= Prod.ext (show L.fst=t.fst from (congr_arg (Prod.fst (β:=Manner m)) he)) (Subtype.ext (congr_arg Prod.snd he)); subst L
    exact (masked_eq _ _ _ _ (Disjoint.mono_left hp hh)).symm
  · exact False.elim (h hz.symm)
  · exact False.elim (hz hh'.symm)
  rfl
end YM.Next.Rank.Flux
