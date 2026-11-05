import YM.AnalyticBridge.LOCAL_GAUSSIAN_MULTIPLIER.Exponent
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Opacity.Compression
/-! # Before any integration. Local-impact budget grammar for the film. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Pump
open Function Lattice RG Pressure Tree Wilson AnalyticBridge.GaussianFieldAlignment Locations Channels
open Matrix Finset PhysicalGuard7f546.Curved Next.SectorChange Precision AnalyticBridge.LocalGaussianLaws Filter
    SectorTools.PhysicalGaussianSwitch AnalyticBridge.RelativeLogdet Physical Push.Local
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {c f : Side} {G : Gauge} {S : StepData c f} {x : ℝ} {A B : Stores S}
    {F F' : Forest S.ratio} {k k' : S.Choices} {U V : Config G c} {i : Site c} {X X' : Support c} {p q : Pilot G S x}

def Matched (p : Pilot G S x):= Positioned x p.key p.view
lemma Matched.signed (h : Matched p) (e : Wheel c) : Matched (spires e p):= turns_marks e.1 e.2 p.key p.view _ h
lemma Matched.bright (h : Matched p) (v : Site c→ G.El): Matched (burnish v p):= Positioned.turn h v

-- Hears dust only AFTER both endpoints are purchased (symmetric criterion).
def Span (p : Support c) (x : ℝ) (S : StepData c f) (i : Bond f):= ∀ j∈Next.SectorChange.points S i, Shields p j (20*radiusB x+16)

structure Hears (X : Support c) (p q : Pilot G S x) : Prop where
  reads : Physical.Reads X p.key q.key p.park q.park p.view q.view p.tag q.tag
  speaks i : Span X x S i → ∀ t,rods p t i=rods q t i

private lemma signHere (i : Site c) (hp : inspected {i} ⊆ X) (h : Agrees ↑X U V) (hU : Positioned x A U) (hV:Positioned x B V): i∈ A.flags↔i∈ B.flags:= by
  have he := flags_agree (temp x) U V {i} (agrees_mono h (by exact_mod_cast hp))
  rw [← show A.flags=_ from hU,← show B.flags=_ from hV] at he
  simpa using Iff.of_eq (congr_arg (fun a : Support c=> i∈a) he)

lemma back_edge (i : Bond f) (he : Next.SectorChange.points S i ⊆ (X:Set (Site c))) (h : Agrees (X:Set _) U V) : replica S.ratio U i=replica S.ratio V i:= by
  unfold replica; split; exact rfl
  rename_i e
  refine h _ (he (by simp [Next.SectorChange.points])) ?_
  exact Locations.crossing i e ▸ he (by simp [Next.SectorChange.points] : S.ratio.parent (i.1+step i.2)∈Next.SectorChange.points S i)



def pushed (e : Wheel c) (X : Support c):= X.map (orient e).toEmbedding
lemma seat (e : Wheel c) {j : Site c} (h : j∈X): orient e j ∈ pushed e X:= mem_map_of_mem _ h
lemma safe (e : Wheel c) {n : ℕ} (h : Shields X i n): Shields (pushed e X) (orient e i) n:= by
  intro j hj; obtain ⟨j,rfl⟩ := (orient e).surjective j; exact seat _ (h j ((moving e i j).symm.trans_le hj))
lemma across (i:Bond f) (e : Wheel c) (h : Span X x S i): Span (pushed e X) x S (sendEdge e.1 (S.ratio.embed e.2) i):= by
  intro j hj; rw [Tensor.moves_points] at hj; obtain ⟨j,hj,rfl⟩:=hj
  exact safe e (h j hj)
lemma advert (h : Hears X p q) (hp : X' ⊆ X): Hears X' p q := by
  obtain ⟨h,hc⟩:= h; exact ⟨⟨agrees_mono h.configuration (by exact_mod_cast hp),fun i hi=>h.frame _ (hp hi),fun i hi=>h.bond _ (hi.trans hp),fun j hi he=>h.tree j (hp hi) (hp he), fun i hi=>h.flags _ (hi.trans hp),fun i hi=>h.cost _ (hi.trans hp),fun i hi=>h.aisle _ (hi.trans hp)⟩,
     fun i hi=>hc i fun j hj k hk=>hp (hi _ hj k hk)⟩
lemma Steam (h : Hears X p q) (v : Site c→G.El) : Hears X (burnish v p) (burnish v q):= by
  obtain ⟨h,hc⟩:=h; refine ⟨⟨fun i hi hh=>?_,h.frame,h.bond,h.tree,h.flags,h.cost,h.aisle⟩, fun i hi g=>?_⟩
  · simp only [burnish,Lattice.gauge,h.configuration i hi hh]
  rw [burn,burn]; simp only [Lattice.gauge,hc i hi g]
lemma lap (e : Wheel c) (h : Hears (pushed e X) p q) (hp : Matched p) (hq : Matched q) : Hears X (spires e p) (spires e q):= by
  obtain ⟨h,hZ⟩:=h
  let Z:= pushed e X; let l':= spires e p; let k':= spires e q; let s:=e.1; let b:=e.2
  have hl: Agrees ↑X l'.view k'.view:= by
    apply Push.Local.agrees_pull (U:=p.view) (V:=q.view) s b
    rw [← show pushed e X=X.image (Push.Local.turnSites s b) from Finset.map_eq_image ..]; exact h.configuration
  have hs (i) (hv : pinPos i ⊆X) : pinPos (sendEdge e.1 e.2 i) ⊆ Z:= by
    rw [pin_map]; intro j hj; obtain ⟨j,he,rfl⟩:= mem_image.mp hj; exact seat _ (hv he)
  refine ⟨⟨hl,fun i hi=>congr_arg (S.patch.orient e.1).symm (h.frame _ (seat e hi)),fun i hi=>congr_arg ((S.patch.offset e.1).symm : S.patch.Points→ _) (h.bond _ (hs i hi)),fun i hi hx=>?_,fun i hi=>signHere i hi hl (hp.signed e) (hq.signed e),fun i hi=>?_,fun i hi=>?_⟩, ?_⟩
  · let z:= sendEdge s (S.ratio.embed b) i; have hz y (hy : y∈Next.SectorChange.points S z): y∈Z:= by
      unfold z at hy; rw [Tensor.moves_points] at hy
      obtain ⟨j,hj,rfl⟩:=hy; exact seat e (by simp only [Next.SectorChange.points,Set.mem_insert_iff,Set.mem_singleton_iff] at hj; rcases hj with rfl|rfl; exact hi; exact hx)
    exact (trunk_map s b ..).trans ((h.tree z (hz _ (by simp [Next.SectorChange.points])) (hz _ (by simp [Next.SectorChange.points]))).trans (trunk_map ..).symm)
  · simp only [spires,book,mem_map_equiv,Equiv.symm_symm]
    refine h.cost _ ?_; rw [start_map]; intro j hj
    obtain ⟨j,he',rfl⟩:= mem_image.mp hj; exact seat e (hi he')
  · simp only [spires,book,mem_map_equiv,Equiv.symm_symm]; exact h.aisle _ (hs i hi)
  intro i hi g; rw [shooting,shooting,Channels.read_back,Channels.read_back,hZ _ (across i e hi) g]

-- specialize to the globally sampled forest schedule
lemma recall {O : Orchard S} {k l : Streak O} {Y : RoomView A x k.wood G} {Z : RoomView B x l.wood G}
    (hp : Nearby X U V A B k l) (h : InteractingRank.nearby X Y = amplify hp Z) (hU : Positioned x A U) (hV : Positioned x B V):
    Hears X ⟨A,k.wood,k.tag,U,Y⟩ ⟨B,l.wood,l.tag,V,Z⟩:= by
  refine ⟨⟨hp.branch,hp.keys.1,fun i hi=>hp.keys.2 i (hi (by simp [pinPos])) (hi (by simp [pinPos])),fun i hi _=>hp.trunk_iff i hi,fun i hi=>signHere i hi hp.branch hU hV,
    fun i hi=>hp.costs i (Finset.not_disjoint_iff.mpr ⟨S.ratio.parent i.1, Finset.mem_image_of_mem _ (Work.E01.base_touched _),hi (Finset.mem_image_of_mem _ (Work.E01.base_touched _))⟩),
    fun i hi=>hp.aisles i (Finset.not_disjoint_iff.mpr ⟨i.1,by simp [pinPos], hi (by simp [pinPos])⟩)⟩,?_⟩
  intro i hi g
  have hu:lumen S x X i:= hi _ (by simp [Next.SectorChange.points])
  change kid U Y g i=kid V Z g i
  by_cases hq : i∈k.wood.trunks
  · have he : i∈l.wood.trunks:= (hp.trunk_iff i hu.center).1 hq
    exact (k.wood.on_tree _ ⟨i,hq⟩).trans (l.wood.on_tree _ ⟨i,he⟩).symm
  let a:k.wood.Free:= ⟨i,hq⟩; let b:l.wood.Free:= ⟨i, mt (hp.trunk_iff i hu.center).mpr hq⟩
  have hf:= hp.frozen (i:=a) hu (j:=b) rfl
  by_cases he : chill A x k.wood a
  · let c : Frozen A x k.wood:=⟨a,he⟩; let d:Frozen B x l.wood:=⟨b,hf.1 he⟩
    rw [show kid U Y g i=Y.1 c from (k.wood.off_tree _ a).trans (freeze_held (j:=c) ..), show kid V Z g i=Z.1 d from (l.wood.off_tree _ b).trans (freeze_held (j:=d) ..),Nearby.iced h c hu d rfl]
  let c: Active A x k.wood:=⟨a,he⟩; let d: Active B x l.wood:=⟨b,hf.not.mp he⟩
  have hu:tape (0+g • Y.2) c=tape (0+g • Z.2) d:= by
    ext i; change 0+g*Y.2 _=0+g*Z.2 _; rw [Nearby.flammable h c hu d rfl]
  have hl:kid U Y g i=G.lieExp (tape (0+g • Y.2) c)*replica S.ratio U i:= (k.wood.off_tree _ a).trans (freeze_regular (j:=c) ..)
  have hr:kid V Z g i=G.lieExp (tape (0+g • Z.2) d)*replica S.ratio V i:= (l.wood.off_tree _ b).trans (freeze_regular (j:=d) ..)
  rw [hl,hu,back_edge i (show _ from fun p hp=> (hi _ hp).center) hp.branch, hr]
end YM.PhysicalNext.InteractingRank.Pump
