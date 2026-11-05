import YM.TraceExtension.Turret.Apt
import YM.TraceExtension.Perfect.Zippy
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Turret
open Function Filter Matrix Lattice Precision Laurent Stationary Perfect Exterior Tree RG Wilson Finset Push.Uniform Det Planned.PrimaryIntegral295 Lamp Extra.Iteration
open WardBin Filch PhysicalNext.JointLoad AnalyticBridge.SectorAffine.Offset Planned.AtomRegular.Foliage Next.Fluctuations Next.SectorChange
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{n:Side}{k r:ℕ}{o x y:Site n}{p q C E D a v:ℝ}
structure Splendor (X:Peat G n)(P:Support n)(k:ℕ)(A C:ℝ):Prop where
    cloth:X∈ loom G n
    locale : LocalOn P X
    symm : GaugeInvariant X
    lit(U:Config G n) : ContDiffAt ℝ ω (X ∘ increment U) 0
    tickets (Y:Type)[NormedAddCommGroup Y][NormedSpace ℝ Y](W:Y→ Config G n)(x:Y) : (∀ i, Allows k (fun v=>G.mat (W v i)) x C)→ Allows k (X ∘ W) x A
section
variable {X Y:Peat G n}{P Q:Support n}
lemma spark_zero (h:0 ≤ a):Splendor (0:Peat G n) P k a C:=⟨(loom ..).zero_mem,fun _ _ _=>rfl,fun _ _=>rfl,fun _=>contDiffAt_const,fun V _ _ _ _ _=> allows_const _ ((norm_zero (E:=ℝ)).trans_le h)⟩
lemma Splendor.up (h:Splendor X P k a C)(he:P⊆Q)(ht:a≤p): Splendor X Q k p C:=⟨h.cloth, fun U V hx=> h.locale _ _ (agrees_mono hx he),h.symm,h.lit,fun V _ _ W y H=> (h.tickets V W y H).mono ht⟩
lemma Splendor.plus (h:Splendor X P k a C)(he:Splendor Y P k p C):Splendor (X+Y) P k (a+p) C:=⟨(loom _ _).add_mem h.cloth he.cloth,fun _ _ hp=> congr_arg₂ (· + ·) (h.locale _ _ hp) (he.locale _ _ hp),fun _ _=>congr_arg₂ (· + ·) (h.symm ..) (he.symm ..),fun U=>(h.lit U).add (he.lit U),fun V _ _ W y H=> (h.tickets V W y H).add (he.tickets V W y H)⟩
lemma Splendor.scale(c:ℝ)(h:Splendor X P k a C): Splendor (c • X) P k (|c| *a) C:= ⟨(loom _ _).smul_mem _ h.cloth,fun _ _ hp=> congr_arg (c •·) (h.locale _ _ hp),fun _ _=>congr_arg (c •·) (h.symm ..),fun U=>(h.lit U).const_smul (c:=c),fun V _ _ W y H=> (h.tickets V W y H).smul c⟩
lemma Splendor.lapse(h:Splendor X P k a C)(he:Splendor Y P k p C):Splendor (X-Y) P k (a+p) C:=by simpa [sub_eq_add_neg] using h.plus (he.scale (-1))
lemma sparkle {V:Type}(X:V→ Peat G n)(s:Finset V)(c:V→ℝ)(h:∀ i∈s,Splendor (X i) P k (c i) C):Splendor (∑ i∈s,X i) P k (∑ i∈s,c i) C:=by induction s using Finset.induction with
   | empty=>simpa using spark_zero (G:=G) (P:=P) (k:=k) (C:=C) le_rfl
   | insert i s hi ih=>rw [sum_insert hi,sum_insert hi]; exact (h i (mem_insert_self ..)).plus (ih fun j hj=>h j (mem_insert_of_mem hj))
private lemma move_g (i:Site n)(U:Config G n)(u:Coats G n): ride i (Lattice.gauge u U)= Lattice.gauge (fun x=>u (x+i)) (ride i U):=by ext1 j; unfold ride Lattice.translate Lattice.gauge; dsimp only; rw[add_right_comm j.1]
private lemma aware (A:Directions G n)(U:Config G n)(i:Site n): ride i (increment U A)=increment (ride i U) ((ContinuousLinearMap.pi (fun j:Edge (Site n)=> ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _=> G.Color) (rideI i j))) A):=by funext j;rfl
lemma Splendor.trill (h:Splendor X P k a C)(hv: P.image (· + x) ⊆ Q):Splendor (rj x X) Q k a C:=by
    let T: Directions G n→L[ℝ] Directions G n:= ContinuousLinearMap.pi fun j=>ContinuousLinearMap.proj (rideI x j)
    refine ⟨taking_loom _ _ h.cloth,fun U V h'=>h.locale _ _ (fun j ha hb=>?_),fun u U=> ?_,fun U=>?_,fun V _ _ W y H=> h.tickets V (ride x ∘ W) y (fun j=> H (rideI x j))⟩
    · change U (rideI x j)=V (rideI x j); apply h' _ (hv (mem_image_of_mem _ ha))
      change j.1+x+step j.2 ∈ Q; rw [add_right_comm]; exact hv (mem_image_of_mem _ hb)
    · change X (ride x (Lattice.gauge u U))=X _;rw [move_g]; exact h.symm ..
    rw [show (rj x X) ∘ increment U= X ∘ increment _ ∘ T from funext fun i=>congr_arg X (aware i U x)]; exact ContDiffAt.comp (g:=X ∘ increment (ride x U)) _ ((map_zero T).symm ▸ h.lit _) T.contDiff.contDiffAt
end
section
-- difference carried on root-local effects. No periodic gauge seam beyond radius unless projected with guards.
variable {Z Z':Peat G n}
structure Sigh (Z:Peat G n)(o:Site n)(a C:ℝ):Prop where
 cloth:Z∈loom G n
 pay:Estate o (ballX Z) a (fun _=>C)
lemma sigh_zero (h:0 ≤ C): Sigh (0:Peat G n) o a C:= ⟨(loom _ _).zero_mem, ⟨fun i hi hk=>by simp [show ballX (0:Peat G n)=(0:Acr G n→ℝ) from rfl,Perfect.cost,Perfect.leaf,bank,h]⟩⟩
lemma Sigh.plus(h:Sigh Z o a C)(ht:Sigh Z' o a D):Sigh (Z+Z') o a (C+D):=by
    refine ⟨(loom _ _).add_mem h.cloth ht.cloth,⟨fun i hi he=>?_⟩⟩
    have hp:= cost_add (landW o) a 4 0 (leaf (ballX Z) 0 i) (leaf (ballX Z') 0 i)
    refine le_trans (le_of_eq (congr_arg _ ?_)) (hp.trans (add_le_add (h.pay.values i hi he) (ht.pay.values i hi he)))
    funext v; unfold Perfect.leaf bank; rw [show ballX (Z+Z')=ballX Z+ballX Z' from rfl, iteratedFDeriv_add_apply ((loom_read h.cloth).2.2.of_le le_top) ((loom_read ht.cloth).2.2.of_le le_top)];rfl
lemma Sigh.scale(t:ℝ)(h:Sigh Z o a C): Sigh (t • Z) o a (|t| *C):= by refine ⟨(loom _ _).smul_mem _ h.cloth,⟨fun i hi hv=>?_⟩⟩; rw [show ballX (t • Z)=t • (ballX Z) from rfl,cell_fee _ _ _ _ _ ((loom_read h.cloth).2.2)]; exact mul_le_mul_of_nonneg_left (h.pay.values i hi hv) (abs_nonneg _)
lemma Sigh.lapse(h:Sigh Z o a C)(hp:Sigh Z' o a D):Sigh (Z-Z') o a (C+D):=by simpa [sub_eq_add_neg] using h.plus (hp.scale (-1))
lemma sighed {V:Type}(X:V→ Peat G n)(s:Finset V)(c:V→ℝ)(h:∀ i∈s,Sigh (X i) o a (c i)):Sigh (∑ i∈s,X i) o a (∑ i∈s,c i):=by induction s using Finset.induction with
 | empty=>simpa using sigh_zero (G:=G) (o:=o) (a:=a) le_rfl
 | insert i s hi ih=>rw [sum_insert hi,sum_insert hi]; exact (h i (mem_insert_self ..)).plus (ih fun j hj=>h j (mem_insert_of_mem hj))
lemma Sigh.up(h:Sigh Z o a C)(hv:C≤D): Sigh Z o a D:= ⟨h.cloth,⟨fun i hi ht=> (h.pay.values i hi ht).trans hv⟩⟩
lemma Sigh.trill(h:Sigh Z x a C)(v:Site n): Sigh (rj v Z) (x+v) a C:=by refine ⟨taking_loom _ _ h.cloth,⟨fun i hi ht=>?_⟩⟩; rw [ride_ball,ride_jet _ _ _ _ (loom_read h.cloth|>.2.2)]; exact h.pay.values i hi ht
lemma Sigh.lease (h:Sigh Z o a C)(hv:separation x o≤r) (ha:0 ≤ a)(hA:a≤1): Sigh Z x a (Perfect.shelter 1 4 r*C):=by
    refine ⟨h.cloth, ⟨fun j hj hp=> ?_⟩⟩
    refine le_trans ?_ (mul_le_mul_of_nonneg_left (h.pay.values j hj hp) (Perfect.shelter_pos _ _ (by positivity)).le)
    unfold cost; rw [mul_sum]; apply sum_le_sum; intro i _; rw [← mul_assoc]; apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    have hb:limitN (landW x) i ≤ r+limitN (landW o) i:= (limitN_le _ _).2 (fun k=> by
        rw [a_f]; exact le_trans (separation_triangle x o _) (Nat.add_le_add hv (a_f _ _ _ (i k) ▸ limitN_ge _ i k)))
    apply (spot_mono a 4 0 ha hb).trans; unfold Perfect.spot; simp only [sub_zero]; rw [max_eq_right (by positivity),max_eq_right (by positivity), Nat.cast_add]; exact le_trans (shelter_add a _ (by positivity) (by positivity)) (mul_le_mul_of_nonneg_right (shelter_top ha hA (by positivity) le_rfl le_rfl) ((Perfect.shelter_pos _ _ (by positivity)).le))
end
end YM.Trace.Turret
