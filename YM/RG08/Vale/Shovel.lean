import YM.RG08.Vale.Faire
/-!
# All-orders null cancellation on cover polynomials. No budget leakage
at the projection. Doesn't assert transversality of arbitrary high rank:
it annihilates polynomial tests of TOTAL joint bounded weight. Lifts
need to preserve the full null coordinate across the sequence.
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
noncomputable section
namespace YM.RG08.Vale
open RG Laurent Lattice Wilson Bloch Exterior Push.AbsoluteSums Finset Function Filter
open UVExt.Paths Stationary Planned.PrimaryIntegral295 Place Shade Quire Source Source.Drops Labels Scores Tall
open scoped Topology ContDiff Classical BigOperators
variable {G:Gauge}{p m c: Side}{R:ℝ}{D d e j r n i k t:ℕ} {τ:ℕ}
variable {X : Fin j → Snap G d} {W : Fin j → E4 → G.Color}
variable {F: Labels.Frame G d} {V : BoardU D R G}
set_option maxHeartbeats 600000 in
private lemma expansion {U:Screed ℝ (Loc G 1)}(hu: ∀ i j,Tidy (U i j)) (h : Loom.Shore (0:Site m) τ U) (P:Hol G) (e:ℕ) (X:Fin j→ Snap G d)(W:Fin j→ E4→G.Color) :
    (∑ i∈ range (j+1),iteratedFDeriv ℝ j (rootSong (Loom.strand τ e U i) m 0 ∘ curtain X W m) 0 bony)=
      ∑ i∈ range (j+1),iteratedFDeriv ℝ j (rootSong (Loom.strand τ e U i) m 0 ∘ studio G d m) 0 X := by
  obtain ⟨Y,hY⟩:= Loom.shelved (p:=e) (n:=j+τ) h (by omega) hu
  let Q:= input G m; let A:= curtain X W m; let Z:= rung X; let B:= studio G d m ∘ Z
  have hp : B 0=0:= by simp [B,begins]
  have hV:=curtain_sm X W m
  have hW : ContDiffAt ℝ j B 0 := by
    have hh := (show ContDiffAt ℝ ω (studio G d m) (Z 0) from (map_zero Z) ▸ begins_sm ..).comp _ (Z.contDiff.contDiffAt); exact hh.of_le le_top
  let M:= large (0:Site m) j (Loom.strand τ e U)
  have hm:ContDiff ℝ j M:= (large_smooth ..).of_le le_top
  have ht : Tendsto Q (𝓝 0) (𝓝 1):= by simpa [Q] using input_cont.tendsto (0:Link G m)
  have hA : Tendsto A (𝓝 0) (𝓝 0) := (curtain_root X W m) ▸ hV.continuousAt.tendsto
  have hB : Tendsto B (𝓝 0) (𝓝 0) := hp ▸ hW.continuousAt.tendsto
  have hq : (Y ∘ Q) ∘ A =ᶠ[𝓝 0] (Y ∘ Q) ∘ B:= hY.coast (Q ∘ B) (Q ∘ A) _ _ (ht.comp hB) (ht.comp hA) (overarch X W P)
  have hx (P : Stage j→Link G m) (hP:P 0=0)(ht: ContDiffAt ℝ j P 0) : iteratedFDeriv ℝ j (Y ∘ Q ∘ P) 0 bony=iteratedFDeriv ℝ j (M ∘ P) 0 bony:= by
    change iteratedFDeriv ℝ j ((Y∘Q)∘ P) 0 _= _; rw [Cases.compReads (hP.symm ▸ hY.hol.of_le le_top) ht le_rfl _,Cases.compReads hm.contDiffAt ht le_rfl _]; refine sum_congr rfl fun i _=> ?_; unfold Cases.caseRead; rw [hP]; apply DFunLike.congr_fun
    apply smul_right_injective _ (show ((i.length.factorial:ℝ)⁻¹) ≠ 0 by positivity); exact (hY.scores_at _ (i.length_le.trans (Nat.le_add_right ..))).trans (Loom.large_jet _ _ (fun i=>Loom.strand_tid hu) i.length_le).symm
  let f i := rootSong (Loom.strand τ e U i) m 0
  have hg i : ContDiff ℝ j (f i):= Tensor.diag_smooth ..
  have hy (P:Stage j→Link G m)(ht : ContDiffAt ℝ j P 0) : iteratedFDeriv ℝ j (M∘P) 0 bony= ∑ i∈Finset.range (j+1), iteratedFDeriv ℝ j (f i ∘ P) 0 bony := by
    rw [show M ∘ P=∑ i∈range (j+1), f i∘P from funext fun x=> by
      unfold M f; simp [Quire.large,Function.comp_apply,Finset.sum_apply]]
    rw [iteratedFDeriv_sum_apply (fun i _=> (hg i).contDiffAt.comp 0 ht), _root_.sum_apply]
  have hZ : (∑ i∈Finset.range (j+1),iteratedFDeriv ℝ j (f i ∘ A) 0 bony)=∑ i∈Finset.range (j+1),iteratedFDeriv ℝ j (f i ∘ B) 0 bony := ((hx _ (curtain_root ..) (hV.of_le le_top)).trans (hy _ (hV.of_le le_top))).symm.trans ((DFunLike.congr_fun ((hq.iteratedFDeriv ℝ j).eq_of_nhds) bony).trans ((hx _ hp hW).trans (hy _ hW)))
  apply hZ.trans; apply sum_congr rfl; intro i _
  let O:= f i ∘ studio G d m
  have he:= DFunLike.congr_fun (Next.Foundations.jets_linear Z (show ContDiffAt ℝ j O 0 from (hg i).contDiffAt.comp _ ((begins_sm ..).of_le le_top))) bony
  exact he.trans (congr_arg (iteratedFDeriv ℝ j O 0) (funext fun i=> rung_one ..))
lemma opens (H:Hol G)(h:Marvel τ V)(hp:Lank V)(hg:auditT H F V=0)(g:Cham)(a:Fin j→ℕ)
    (he:(∑ i,a i)+cashT g ≤ d)(hc:∀ i, W i∈Place.rangeLt G.Color (d+1))(hm: ∀ i,throughSlot (X i) (a i))(ht:j≤d)(n:ℕ):
    (∑ i∈range (j+1),vault (Loom.strand τ n (fun j r=>plug (coinsT D g) R∘V j r) i) (floorP X W) bony)=0 := by
  let U j r := plug (coinsT D g) R∘V j r; let Y:=Loom.strand τ n U
  have hz : ∀ i,Tidy (Y i):= fun i=> (roundTrip h (coinsT D g)).toTidy; have hx : ∀ i,Polished (Y i):= fun i=> strandP hp _
  have hv (k) := movie (hz k) (hx k) X
  simp_rw [penny_amt (hz _) (hx _)] at hv -- maybe
  have hw (k):=plenish board_end (hz k) (hx k) (theater X W hc (Nat.le_succ d)) (fun p=> curtain_sm ..) (fun _=> curtain_root ..) bony
  let f (X : ℕ → ℝ) (k : ℕ) := X k
  have ht:= tendsto_nhds_unique_of_eventuallyEq (tendsto_finsetSum (Finset.range (j+1)) fun i _=> hw i) (tendsto_finsetSum (Finset.range (j+1)) fun i _=> hv i) (Eventually.of_forall (fun i=> expansion (U:=U) (fun k j=>Tidy.map _ (h.hem k j)) (h.wardrobe (boards i) _ _) H n X W))
  exact ht.trans (plot _ h hp hg g n X a hm he (by assumption))

def deckP (P : Potential G) (v : Fare G) := scent v.2.2 (P (Place.seat v.1) (heap v).2)
set_option maxHeartbeats 400000 in
lemma pick (H:Hol G)(h:Marvel τ V)(hp:Lank V)(hg:auditT H F V=0)(g:Cham)(n:ℕ)(j:ℕ)
    (A:Fin j→ Place.Potential G)(a:Fin j→ℕ)(ha:∀ i,0<a i)(hw:(∑ i,a i)+cashT g ≤d)(hA : ∀ i,A i∈Place.rangeLt (Axis→G.Color) (a i)):
    wallet (Loom.strand τ n (fun k r=>plug (coinsT D g) R∘V k r) j) (fun i=> deckP (A i))=0 := by
  induction j using Nat.strong_induction_on with
  | h j ih=>
    let P:=Loom.strand τ n (fun k r=>plug (coinsT D g) R∘V k r)
    have he : (∑ i,a i)≤d := (Nat.le_add_right ..).trans hw
    have ht i:= (single_le_sum (fun i _=>Nat.zero_le (a i)) (mem_univ i)).trans he
    choose W X hW hX Hx using fun i=> generated (A i) (hA i) (ht i)
    let f := floorP X W
    let O (c:OrderedFinpartition j)(i:Fin c.length)(v:Fare G) := iteratedFDeriv ℝ (c.partSize i) (f v) 0 (bony ∘ c.emb i)
    have hv := opens H h hp hg g a hw (fun i=> grows _ (Nat.add_le_add_right (ht i) 1) (hW i)) hX ((Cases.arity ha).trans he) n
    let V(c:OrderedFinpartition j):= (c.length.factorial:ℝ)* wallet (P c.length) (O c)
    have hh: ∑ c,V c=0 := by
      unfold vault at hv; rw [sum_comm] at hv
      refine Eq.trans (Finset.sum_congr rfl fun c _=>?_) hv
      symm; rw [sum_eq_single c.length]; swap; · intro i _ hi; unfold penny; rw [grant_else hi.symm]; simp
      swap; · simp [c.length_le]
      unfold penny; rw [grant_self]
    have hy(c:OrderedFinpartition j) (hc:c ≠ .atomic j) : V c=0 := by
      let e:= Cases.costs c a
      have hL := lt_of_le_of_ne c.length_le (fun hl=> hc (Cases.finest c hl))
      let S (i:Fin c.length) (x:E4) (y:Axis):= iteratedFDeriv ℝ (c.partSize i) Place.logo (0:Place.EdgeRead G d)
           (fun j=> let b:= c.emb i j; (W b x, Place.jump (W b) x y, Place.road x y (X b)))
      have hm : ∀ i,S i∈ Place.rangeLt _ (e i):=fun i=> Place.vector_band _ (fun y=> Place.logo_cost d (W∘c.emb i) (X∘c.emb i) (a∘c.emb i) y (fun s=>ha _) (fun s=>hW _) (fun s=> hX _))
      have he: O c=fun i=> deckP (S i):= by
        funext i v; exact (motionD (supportAt X W v.1 (v.1+step (heap v).2) (heap v).2) _ (c.partSize i) (bony ∘ c.emb i)).trans
          (congr_arg (scent _) (DFunLike.congr_arg (iteratedFDeriv ℝ (c.partSize i) (Place.logo (G:=G) (d:=d)) 0) (funext fun t=> align ..)))
      have hC : ∑ i,e i=∑ i,a i:=Cases.all c a
      unfold V; rw [he]; rw [show wallet (P _) _=0 from ih c.length hL S e (Cases.live _ ha) (by rw [hC]; exact hw) hm,mul_zero]
    rw [sum_eq_single (.atomic j)] at hh; swap; · exact fun _ _ he=>hy _ he
    swap; · simp
    let c:=OrderedFinpartition.atomic j
    have hy i : O c i=deckP (A i) := by
      unfold O; funext v; change iteratedFDeriv ℝ 1 _ _ _=_; rw [iteratedFDeriv_one_apply]; exact (summonsP ..).trans (congr_arg (fun x : Potential G=>deckP x v) (Hx i).symm)
    change (j.factorial:ℝ)*wallet (P j) (O c)=0 at hh; rw [funext hy] at hh; exact (mul_eq_zero.mp hh).resolve_left (by positivity)
theorem shot (H:Hol G)(h:Marvel τ V)(hp:Lank V)(hg:auditT H F V=0)(g:Cham)(n j:ℕ)(A:Fin j→ Potential G)
    (a:Fin j→ℕ)(hw:(∑ i,a i)+cashT g ≤d)(hA : ∀ i,A i∈Place.rangeLt (Axis→G.Color) (a i)):
    wallet (plug (coinsT D g) R∘ V n j) (fun i=> deckP (A i))=0 := by
  by_cases ht:j≤τ+n; swap; · rw [not_ne_iff.mp (mt (h.cap n j) ht)]; simp [wallet]
  have hs (φ:Exam D)(n:ℕ)(j:ℕ)(ht:j≤τ+n): Loom.strand τ (τ+n-j) (fun n j=> plug φ R ∘ V n j) j=plug φ R∘ V n j := by unfold Loom.strand; rw [if_pos (by omega),show τ+n-j+j-τ=n by omega]
  rw [← hs _ _ _ ht]
  by_cases hx : ∀ i, 0<a i
  · exact pick H h hp hg g _ _ A a hx hw hA
  push Not at hx; obtain ⟨i,hi⟩:=hx; have he:= hA i; rw [show a i=0 by omega,Place.rangeLt,Submodule.mem_bot] at he
  unfold wallet; simp_rw [show ∀ b:Beads (Loc G 1) j, (∏ i,deckP (A i) (b i))=0 from fun b=> Finset.prod_eq_zero (mem_univ i) (by rw [he]; exact map_zero _),mul_zero]; simp
end YM.RG08.Vale
