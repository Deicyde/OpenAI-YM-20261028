import YM.Next.MULTISOURCE.Journey

/-!
# Actual ride with same history activities.

Evaluate only true `Bands.Active`. Use full family of `v`, signs included;
stance argument lets the physical cylinders be applied through pulls.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Multi
open RG Wilson Lattice Function Filter Finset Marker Overlay Stock MeasureTheory Source Labels Mix
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical

variable {G : Gauge} {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] {R : Census V}
variable {C : Family G} {N i k p d : ℕ} {o : ∀ j,V→Site (C.side j p)} {v : V→C.label d}
variable (H : C.Makes) {b : ℝ}

structure Passage {N p d i : ℕ} (C : Family G) (w : ℕ→ℝ) (x : ∀ j,V → Site (C.side j p))
    (F : V→ Config G (C.side N p)→ℂ) (L : Lane C.path R N p) : Prop where
  scope : L.Works i
  stance : L.load=fun _ => d
  exactF : L.uses=F
  anchored j : i ≤ j → j ≤ N → (L.sites j).origins=x j
  holds j : i≤j → j ≤ N → Stubs.Holds (L.sites j) (w j)

include H
lemma rides {X} (Hk : Rolling C R v o k i N X) (hv : ∀ m,i≤m → m ≤ N → Locale C d k b m)
    (ht : ∀ m,i≤m → m ≤ N → Spaced (o m) (C.path.levels.clock.coverSize m)) (hh : i≤N)
    (hq : ∀ j,i≤j → j < N → ∀ k,(C.path.levels.clock.op j p).ratio.embed (o j k)=o (j+1) k)
    (h : C.ref d ≤ N) :
    ∃ L : Lane C.path R N p, Passage (d:=d) (i:=i) C (width C 1 k) o (fun i => C.O N p (v i) (o N i)) L := by
  classical
  let J := C.path
  let w := width C 1 k
  have he (j : ℕ) : ∃ A : Bands R (J.rep N p j), i≤j → j≤N → A.origins=o j ∧
      Stubs.Holds A (w j) ∧ A.density=many (J.rep N p j) R (X j) := by
    by_cases h : i≤j ∧ j≤N
    · obtain ⟨f,-,hg⟩ := Hk.accepts j h.1 h.2; have hD := (H.wilson.represents N p j h.2)
      have hP := hv j h.1 h.2
      obtain ⟨A,HA⟩ := imprint (hP.buckets N p h.2) hg (Wage.width_positive ..) (money_accepted ..).2
        (by rw [hD.vac]; exact ht j h.1 h.2) (by rw [hD.vac]; exact hP.adept.1) hD.good.labels
      exact ⟨A, fun _ _ => HA⟩
    -- filler never read
    exact ⟨⟨o j, 0, fun _ => ∅, fun _ => R.quiet, 0,fun _ _ => R.quiet, 0⟩,fun a b => False.elim (h ⟨a,b⟩)⟩
  choose A hA using he
  let L : Lane J R N p := ⟨A,fun _ => d,fun a => C.O N p (v a) (o N a)⟩
  refine ⟨L,⟨⟨hh,?_,?_,?_,?_,?_⟩,rfl,rfl,fun j hj h => (hA j hj h).1,fun j hj h => (hA j hj h).2.1⟩⟩
  · intro j hj hk; have HE := (hA j hj hk).2.1
    exact ⟨HE.ready,_,_,_,_,_,Work.I02.answer Work.I01.answer _ _ _ _ _ _ (w j) (Wage.width_positive ..) HE⟩
  · intro j k he hi
    change _=(A j).origins k
    change (C.path.levels.clock.op j p).ratio.parent ((A (j+1)).origins k)=_
    rw [(hA j he hi.le).1,(hA (j+1) (he.trans j.le_succ) hi).1,← hq j he hi k]
    exact Ratio.embed_parent ..
  · intro s
    refine continuous_integrable _ ?_
    exact continuous_finsetProd s.val fun i hi => C.continuousO ..
  · intro s U
    let F a := Single.cache C (v a) (o N a)
    change ((A N).density U).part s= _
    rw [(hA N hh le_rfl).2.2,Hk.starts,first_prepare _ _ (H.wilson.represents N p N le_rfl).good.labels]
    · simp_rw [Single.cache_full H _ h]
      unfold Ride.Product Ride.bump
      change (↑((C.path.rep N p N).eval _):ℂ)* (∏ i∈_,_)=_
      rw [(H.wilson.starts N p).2,prod_mul_distrib]; ring
    intro i; exact Single.cache_weight H _ (v i)
  · intro j hj hJ s
    change (fun U => ((A j).density U).part s)=(Ride.bump _ s _) • (C.path.levels.clock.op j p).push (C.path.β N p (j+1)) (fun U => ((A (j+1)).density U).part s)
    rw [(hA j hj hJ.le).2.2,(hA (j+1) (hj.trans (Nat.le_succ j)) hJ).2.2]
    rw [Hk.exacts _ hj hJ s]; unfold Ride.bump touch
    push_cast; change _=(∏ _i∈s.val,((C.S.block j).val:ℂ)^d) • _; rw [prod_const]
end YM.Multi
