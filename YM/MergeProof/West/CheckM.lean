import YM.MergeProof.West.Flag
import YM.Next.RANK.Flux.Carrier


/-!
# Clean sum in the rooted output recipe
Use on g_Q only. Lead calculation on TRUE argument frames, kernel-owned. -/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Flux
open Tapes.West
open Marker Glyph Exponential Finset Lattice Ac Relation Value Corona RG Wilson MeasureTheory Tapes Spindle Atlas Station Peak Cells Perch
open scoped BigOperators Classical

variable {V ι κ α β : Type} {G : Gauge} {n : Side} {c : Family G} {i k N p m a b q : ℕ} {s η : ℝ}

variable {Q : BudgetPoint} {hk : i<k} {x : Points m} {hN : k≤N} {hl : middle c.path.levels s k ≤ i} {X : Course c N p k} {R : Lead G c.S p}
local notation "ζ" => readers (C:=c) (b:=s) (p:=p) x X.allow (hk.le.trans X.allow)
variable [Fintype ι] [Fintype κ]
variable (S : ι→Plug G ζ Q.threshold) (P : κ → Lining G ζ Q.threshold) (f : ι→Prop)

lemma s_ated {P' : BudgetPoint} (B : ι→ SourceAt G ζ) (Y : IgnFt R s x X hk hl q b P' Q η) (t : Bale c k s p b x hk.le) (U) (hh)
    (u : PatchPt x s c.path.levels p b (show i+1≤k from hk) → Config G (c.side (i+1) p)→ℂ) 
    (ht : ∀ v:ι, let W:=B v; Carport (b*Q.B) W (q*Q.B))
    (hr : roomTest c.path.levels s k p b q) (hv : Fit c.path.levels s k x) (ha : Allowed c.path.levels s k)
    (hm : Q.B=Perch.walls (clim c.path.levels i))
    -- input correlation BEFORE any marked log
    (Hp : let z:= litFt p X.allow s c t.1 t.2.val
          bed z.val (Poly.pass (∑ i,(B i).amount Q.threshold U))= bed z.val (insertAt t.1 (planterFt (Y.tag t U hh) u))) :
    let z:= litFt p X.allow s c t.1 t.2.val
    let T:= leadFt (Y.tag t U hh) u
    ∑ j:ι,(if (B j).fires=z then (B j).value U else 0)= T.part (tag t.2.val).val:= by
  intro z T
  let D := ∑ i,(B i).amount Q.threshold U
  have hq:D.part (quiet _)=0:= by unfold D; rw [Poly.part_sum]; exact sum_eq_zero fun i _=> asleep _ (B i).chosen _
  have hp:Expands D (Poly.pass D):= ⟨hq,rfl⟩
  have he : Expands T (planterFt (Y.tag t U hh) u):= connected_spec ..
  have H : Expands (insertAt t.1 T) (insertAt t.1 (planterFt (Y.tag t U hh) u)):= by
    refine ⟨(insert_quiet ..).trans he.1,(insert_pass _ _ he.1).trans ?_⟩; exact congr_arg _ he.2
  have hl1 : bed z.val D = bed z.val (insertAt t.1 T):= by apply (bedrock z.val hp).uniq; refine ?_;apply Hp ▸ bedrock z.val H
  have hD : D.part z=T.part (tag t.2.val).val:= by
    rw [← show _=D.part z from (shelve _ _ _).trans (if_pos (subset_refl z.val)),hl1,shelve,if_pos (subset_refl _), insert_part]
    change (if homes {t.1} (Glyph.push t.1 _) then _ else 0)=_; rw [if_pos (settle ..)]; change T.part (fibre _ (Glyph.push t.1 _))=_;rw [dock]
  apply Eq.trans _ hD; unfold D; rw [Poly.part_sum]; apply sum_congr rfl; intro j _; unfold SourceAt.amount; rw [Poly.part_send]; split_ifs with hz h hh'
  · obtain ⟨L,hx,hp⟩:= Tapes.West.f_pair (hN:=X.allow) (hk:=hk.le) hl hr hv ha (B j) _ hm (ht j)
    have he := Tapes.West.torches X.allow s p (C:=c) (a₁:=(L.1,L.2.val)) (a₂:=(t.1,t.2.val)) (hx.symm.trans hz)
    have hg : L=t:= Prod.ext (show L.fst=t.fst from (congr_arg (Prod.fst (β:=Manner m)) he)) (Subtype.ext (congr_arg Prod.snd he)); subst L
    exact (masked_eq _ _ _ _ (Disjoint.mono_left hp hh)).symm
  · exact False.elim (h hz.symm)
  · exact False.elim (hz hh'.symm)
  rfl
end YM.Next.Rank.Flux
