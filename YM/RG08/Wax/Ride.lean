import YM.RG08.Wax.Insert
import YM.RG08.Wax.Laminate
/-!
# Banach addressed heat at distinct slots
Absolute field positions; one step. East-Oriented polygon presentation on evaluated
functionals, in ACTUAL closure norm. No variation allowed across torus branches.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.RG08.Wax
open Function Filter RG Lattice Laurent Stationary Quire Analysis Shade Vale Bands Loom Next.Free Bloch Scores
open scoped Topology BigOperators Real Classical
variable {I X:Type}[Fintype I][DecidableEq I][Fintype X][DecidableEq X] {D s r i j : ℕ}{R:ℝ}{T V W:Finset I}{p:Option Side}{K:Row X X}

abbrev sampleK (T : Finset I)(x : I→ Sight D R): Poise T D R→L[ℝ] ℝ := ContinuousLinearMap.apply ℝ ℝ (speak T x)
lemma tapUni {Y : Type}{A B:Y→Poise T D R}(h:∀ x,sampleK T x ∘ A=sampleK T x ∘ B) : A=B := funext fun i=> spoken fun x=>congr_fun (h x) i

def toneHub (T:Finset I)(A:Rooted (Poise W D R) X r)(B:Rooted (Poise V D R) X s)(x:Beads X r × Beads X s) := sale (A x.1) (B x.2) T
def tape_pair (p:Option Side)(T:Finset I)(K:Row X X)(A:Rooted (Poise W D R) X (r+1))(B:Rooted (Poise V D R) X (s+1))(x: Beads X (r+1)× Beads X (s+1)) := bob p K x • toneHub T A B x
def wounds (p:Option Side)(T:Finset I)(K:Row X X)(A:Rooted (Poise W D R) X (r+1))(B:Rooted (Poise V D R) X (s+1)) := sew (syl r s • tub (tape_pair p T K A B) stemPair)
variable {A:Rooted (Poise W D R) X (r+1)}{B:Rooted (Poise V D R) X (s+1)}
private lemma fundsPair {α β W Z:Type} [NormedAddCommGroup W][NormedAddCommGroup Z]{F:α→W}{H:β→Z}(h: Pens F)(he:Pens H): Summable (fun i:α × β=> ‖F i.1‖ * ‖H i.2‖) := by
   exact summable_mul_of_summable_norm (show Summable (fun i=> ‖‖F i‖‖) from h.norm) (show Summable (fun i=> ‖‖H i‖‖) from he.norm)
lemma tonesQ {A:Rooted (Poise W D R) X r}{B:Rooted (Poise V D R) X s}(T:Finset I)(ha:Pens A)(hb:Pens B) : Pens (toneHub T A B):= by
   have he : Summable (fun p: Beads X r × Beads X s => ‖A p.1‖*‖B p.2‖) := fundsPair ha hb
   exact Summable.of_nonneg_of_le (fun i=> norm_nonneg ((toneHub T A B) i)) (fun p=> sale_cost (A p.1) (B p.2) T) he
lemma pairsQ (T:Finset I) (p:Option Side)(ha:Pens A)(hb:Pens B)(h:Whole K): Pens (tape_pair p T K A B):= by
   obtain ⟨w,M,hM,h⟩:=h; apply Summable.of_nonneg_of_le (fun i=>norm_nonneg _) _ ((tonesQ T ha hb).mul_left M)
   intro i; unfold tape_pair; rw [norm_smul]; exact mul_le_mul_of_nonneg_right (stroke_known K h hM.le ..) (norm_nonneg _)
lemma bound_tid (T:Finset I)(p:Option Side)(ha:Pens A)(hb:Pens B)(h:Whole K): Tidy (wounds p T K A B) := Tidy.sewn (((pairsQ T p ha hb h).pours _).scale _)
lemma samples_vany {A : Rooted (Poise T D R) X r}(x:I→Sight D R)(s:ℝ): sampleK T x ∘ (s • A) = s • (sampleK T x ∘ A):= funext fun i=> map_smul (sampleK T x) s (A i)
lemma samples_add {A B : Rooted (Poise T D R) X r}(x:I→Sight D R): sampleK T x ∘ (A+B)=(sampleK T x ∘ A)+(sampleK T x ∘ B):= funext fun i=>map_add (sampleK T x) (A i) (B i)
lemma pair_bill (hR:0≤R)(h:T=W∪V)(hd:Disjoint W V)(ha:Pens A)(hb:Pens B)(hp:Whole K)(x:I→Sight D R) :
   sampleK T x ∘ wounds p T K A B=countP p K (sampleK W x ∘ A) (sampleK V x ∘ B) := by
    rw [wounds,countP,sew_map,samples_vany x, Pens.echo_pool _ (pairsQ T p ha hb hp)]; refine congr_arg sew (congr_arg (_ • ·) ?_); apply congr_arg (tub · _); funext i
    change sampleK T x (bob p K i • toneHub T A B i)=_; rw [_root_.map_smul]; change _* sale (A i.1) (B i.2) T _= _; rw [sells _ _ h hd hR]; exact mul_comm ..

abbrev Turf (I:Type)[Fintype I] (D:ℕ)(R:ℝ)(X:Type) := (T:Finset I)→ ℕ→ Screed (Poise T D R) X
variable {H:Turf I D R X} {S:Canticle X}
open Finset

def taps (p:Option Side)(K:Row X X)(T:Finset I)(A:Spine (Poise W D R) X)(B:Spine (Poise V D R) X) (r:ℕ) := ∑ i∈wheel r, grant r (wounds p T K (A (i.1+1)) (B (i.2+1)))
def spunL (p:Option Side)(K:Row X X)(T:Finset I)(s:Finset I×Finset I)(F:Turf I D R X) (n e r:ℕ) := ∑ z∈wheel n,∑ x∈wheel e,taps p K T (F s.1 z.1 x.1) (F s.2 z.2 x.2) r
def blue (p:Option Side)(K:Row X X)(S:Canticle X)(F:Turf I D R X)(T:Finset I)(n e r:ℕ): Rooted (Poise T D R) X r :=
   jib p K (F T n e (r+2))+ (∑ b∈wheel n,∑ a∈wheel e, Quire.hymn K (F T b.1 a.1) (Refrain K S p b.2 a.2) r)+(1/2:ℝ) • ∑ i∈partners T,spunL p K T i F n e r
lemma blueQ (h:∀ t i j k, Tidy (H t i j k))(hp:Whole K)(hf:Gets S)(T:Finset I)(n e r): Tidy (blue p K S H T n e r):= by
   refine Tidy.plus (Tidy.plus (jib_tidy ((h ..).pens) hp _) ?_) (Tidy.scale ?_ _)
   · exact Tidy.additions fun i hi=> Tidy.additions fun j hj=> hymn_tidy hp (fun i=>(h ..).pens) (fun i=> (refrains_tune hp (fun i j=>(hf.2 i j).1) _ _ _ _).1) _
   exact Tidy.additions fun v hv=> Tidy.additions fun i hi=> Tidy.additions fun j hj=> Tidy.additions fun x hx=> Tidied r (bound_tid T _ ((h ..).pens) ((h ..).pens) hp)
def taps_at (x:I→Sight D R)(H:Turf I D R X) : Topaz I (HeatS X) := fun t i j k=> sampleK t x ∘ H t i j k
lemma blue_cash (x:I→Sight D R)(hp:Whole K)(he:Gets S)(h:∀ t i j k,Tidy (H t i j k))(hv : 0≤R) :
   taps_at x (blue p K S H)=lever p K S (taps_at x H) := by
   let X:= H; funext T i j k
   rw [taps_at,blue,samples_add,samples_add,samples_vany,jib_stays _ p ((h ..).pens) hp,graft,graft]; unfold lever pumpP arches festival choirR peels taps_at; simp only [Pi.add_apply,Pi.smul_apply,Finset.sum_apply]
   refine congr_arg₂ (·+·) (congr_arg₂ (·+·) rfl (sum_congr rfl fun u hu=>?_)) (congr_arg ((1/2:ℝ) • ·) (sum_congr rfl fun u hu=>?_))
   · rw [graft]; exact sum_congr rfl fun i _=> hymn_sound hp (fun i=>(h ..).pens) (fun i=> (refrains_tune hp (fun i j=>(he.2 i j).1) _ _ _ _).1) _ _
   obtain ⟨hT,hU⟩:= (norms_par ..).1 hu; unfold spunL thunder; rw [graft]; simp_rw [Finset.sum_apply]
   refine sum_congr rfl ?_; intro i hi; rw [graft]; refine sum_congr rfl ?_; intro j hj; unfold taps grail; rw [graft]; refine sum_congr rfl (fun b hb=>?_); rw [grant_leaves, pair_bill hv hT hU ((h ..).pens) ((h ..).pens) hp]
end YM.RG08.Wax
