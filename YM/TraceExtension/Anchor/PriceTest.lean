import YM.MergeProof.West.News

set_option autoImplicit false
noncomputable section
namespace YM.Trace.Pull
open MergeProof MergeProof.Ribbons Set Filter Function Analysis Extraction Table Ward Climb Cells Next.UVStress
  Wilson Lattice Around MeasureTheory
open scoped Topology ContDiff BigOperators Classical
variable {G : Gauge} {C : Family G} {F : Extraction.Order} {J k N p : ℕ}

private lemma room (T:Tiling (C.side N p)) (H:T.kind=Kind.link) (u:T.Cell) (x:Site (C.side N p)) (d K : ℕ)
    (hx:x∈T.margin u (K+d)) (z:Cover) (hz:∀ i,(z i).natAbs ≤ K) :
       x-wrap _ z ∈ T.margin u d:= by
   have he (i) : (T.kind.Strict T.side.val (T.coordinated u (x-wrap _ z) i)) ∧
       (d ≤ T.coordinated u (x-wrap _ z) i ∧ T.coordinated u (x-wrap _ z) i+d+T.kind.shift ≤ T.side.val) := by
      let a:= T.coordinated u x i; let b:= Int.toNat ((a:ℤ)-z i)
      have ha:K+d≤a:= (hx.2 i).1
      have hh: a+(K+d)+T.kind.shift ≤ T.side.val:= (hx.2 i).2
      have hp : T.kind.shift=1:=by rw [H]; rfl
      have hv:= hz i
      have hb : b ≤ a+K ∧ a ≤ b+K ∧ (b:ℤ)=(a:ℤ)-z i:=by unfold b; omega
      have hk : T.coordinated u (x-wrap _ z) i=b:=by
         unfold Tiling.coordinated
         have hs : (x-wrap (C.side N p) z) i-T.starts u i=(b:Per _):=by
            have ht : (↑(b:ℤ):Per (C.side N p))=↑b:=by norm_cast
            rw [← ht,hb.2.2]; change (x i-↑(z i))-_= _; push_cast; unfold a Tiling.coordinated; rw [ZMod.natCast_zmod_val]; abel
         rw [hs,ZMod.val_natCast_of_lt]; exact Nat.lt_trans (by omega : b<T.side.val) T.narrow
      rw [hk,H]; change b<T.side.val ∧ d ≤ b ∧ b+d+1 ≤ T.side.val; omega
   exact ⟨fun i=> (he i).1,fun i=>(he i).2⟩

-- adapt acorns. Every exterior spectator remains at original physical label and fixed address in the m-watch. Inserted mark can advance locally.
lemma sails (I : Watch C) (hp : C.Makes) (h : CellHyp C F) (J : ℕ) (hg : I.t≤J) :
    ∃ B : ℝ, 0≤B ∧ ∀ᶠ i : ℕ×ℕ in F.fuse, ∃ hN : J+1 ≤ i.1,
      ∀ f : Config G (C.side i.1 i.2) → ℂ,
      let T := center C.S i.2 ((Nat.le_succ J).trans hN) 0
      Interior (T.chamber 0) f → ∀ k:ℕ,k ≤ i.1 → ∀ (z:ℤ) (a:Axis), |(z:ℝ)* C.S.a k| ≤ C.S.a J/8 →
      let v:= location C.S k i.1 i.2 (z • step a)
      ‖Wilson.moment (C.beta i.1 i.2) (fun x => f x * I.plot i.1 i.2 (translate (-v) x))‖ ≤ T.rootTest (C.beta i.1 i.2) f * B := by
  classical
  have hY := C.S.shrinks.const_mul (24:ℝ)
  rw [mul_zero] at hY
  obtain ⟨j, ⟨A,hA,H⟩, hj, hs⟩ := ((grows h I.q).and ((eventually_ge_atTop (J+1)).and
    (hY.eventually (ge_mem_nhds (C.S.a_pos J))))).exists
  let z := pushSite C.S hg ∘ I.table
  have hD : Injective z := by
    intro i j hx
    apply I.distinct
    change C.S.gridPoint I.t (I.table i)=C.S.gridPoint I.t (I.table j)
    rw [← finer C.S hg (I.table i), ← finer C.S hg (I.table j)]; exact congr_arg _ (show pushSite C.S hg (I.table i) = _ from hx)
  refine ⟨A^I.n,pow_nonneg hA _,?_⟩
  have he : ∀ᶠ i : ℕ×ℕ in F.fuse, Injective ((wrap (C.S.side J i.2)) ∘ z) := by
    rw [Extraction.Order.fused,Extraction.Order.late]; exact (F.per.cofinal.eventually (sparse C.S J z hD)).mono fun r hr => Eventually.of_forall fun s => hr
  have ht : ∀ᶠ i in F.fuse,imageBudget I.q A j i.1 i.2 := H
  filter_upwards [he,ht] with i hh hg'
  obtain ⟨N,p⟩ := i; let X := C.side N p
  have hq : j≤N := hg'.1; let he: J ≤ N:= (Nat.le_succ _).trans (hj.trans hq)
  let T := center C.S p he 0
  let g (s : Fin (I.n+1)) : T.Cell := wrap (C.S.side J p) (z s)
  let d := 3 * Cells.span C.S hq p
  refine ⟨hj.trans hq,?_⟩; intro f t hI k hK w a hW v
  change k ≤ N at hK
  let L:= C.S.toDepth hK p; let Z:Cover:= L.count.val • (w • step a)
  have heq : v=wrap _ Z:=by unfold v Cells.location; rw [dif_pos hK]; exact L.embed_wrap ..
  let K:= L.count.val*w.natAbs
  have hZ(i:Axis) : (Z i).natAbs ≤ K:=by by_cases h:i=a <;> simp [Z,K,h,Int.natAbs_mul]
  have hd : K+d≤T.side.val/3 := by
    have hu:= C.S.a_pos
    apply (Nat.le_div_iff_mul_le (by decide)).2; apply (Nat.cast_le (α:=ℝ)).1
    apply le_of_mul_le_mul_left _ (C.S.a_pos N)
    rw [show C.S.a N * T.side.val=C.S.a J from C.S.embeds_scale T.units]
    rw [abs_mul,abs_of_pos (hu k)] at hW
    have h0 : C.S.a N * K ≤ C.S.a J/8:=by unfold K; rw [Nat.cast_mul,← mul_assoc,C.S.embeds_scale L, mul_comm]; simpa using! hW
    have h1 : C.S.a N * d ≤ C.S.a J/8:=by unfold d; push_cast; linarith only [hs,C.S.embeds_scale (C.S.toDepth hq p)]
    push_cast; linarith only [h0,h1,hu J]
  have hv s : I.among N p s-v∈ T.margin (g s.succ) d := by
    unfold Watch.among; rw [← location_down C.S hg (by omega) (I.x s), heq]
    exact room T rfl (g s.succ) _ d K (Lease.fewer T _ hd (buffer C.S J he p (pushSite C.S hg (I.x s)))) Z hZ
  choose U hU hQ hB using fun (s : Fin I.n) =>
    Lease.alive (T:=T) hp s (I.among N p s-v) hg' hq (inherits (by omega : J≤j) hq) (hv s)
  let D : Fin (I.n+1) → Config G X → ℂ := Fin.cons f U
  have hi : ∀ (i : Fin (I.n+1)), Interior (T.chamber 0) (D i) := Fin.cases hI hQ
  have hw (x) : (∏ i : Fin (I.n+1), T.copy (g i) (D i) x)= f x * I.plot N p (translate (-v) x) := by
    have hi : g 0=0 := by dsimp only [g,z, Function.comp_apply]; rw [Watch.table, Fin.cons_zero,pushSite,smul_zero,map_zero]; rfl
    rw [Fin.prod_univ_succ,hi,T.copy_zero]; congr 1
    refine Finset.prod_congr rfl fun j _ => (congr_fun (hU j) x).trans (show C.seen (I.q j) (I.among N p j-v) x=C.seen (I.q j) _ _ from ?_)
    rw [sub_eq_add_neg]; exact (C.translation ..).symm
  let β := C.beta N p
  have hx := T.planted (h.all _ _) g hh D hi
  simp_rw [hw] at hx
  apply hx.trans; rw [Fin.prod_univ_succ]
  refine mul_le_mul_of_nonneg_left ?_ (T.root_nonneg β f)
  calc
    _ ≤ ∏ _ : Fin I.n,A := Finset.prod_le_prod (fun i _ => T.root_nonneg β (U i)) (fun i _ => hB i)
    _ = _ := by simp
end YM.Trace.Pull
