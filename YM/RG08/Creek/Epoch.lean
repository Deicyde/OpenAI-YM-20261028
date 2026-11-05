import YM.RG08.Creek.Shape
import YM.RG08.Harvest.Plum
/-! # Multi through capture geometries and agreement with unmasked prior Prop pol. Full root measurements. -/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.RG08.Creek
open Function Finset Filter RG Lattice Laurent Quire Vale Bloch Next.Free Stationary Shade Wax Town Bands Plot Needle Tall Scores Push.AbsoluteSums Work.F08 Door Analysis
open Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset RG Bloch Conductor Staffer Reflect UVExt.Paths Summit Wings High Pill Taste Run PowerSeries Harvest
open scoped Topology ContDiff BigOperators Real Classical Matrix
variable {I:Type}[Fintype I][DecidableEq I]{G:Gauge}{X:Chain}{m N k i j t D:ℕ}{R:ℝ}{a b:I→ℕ}{p:List I}{ν:G.ColorIndex}{D':ChartRatio G}
lemma listed_s (h:p.Nodup) : vanes a p.toFinset=loadᵣ a p:= by
   induction p with
   | nil=> simp [Bands.loadᵣ]
   | cons a' p ih=>
     have hz:=List.nodup_cons.mp h; change _=a a'+loadᵣ a p; rw [← ih hz.2]; unfold vanes; rw [List.toFinset_cons,sum_insert]; simpa using hz.1
lemma ledger_sense {U:Layouts I G D R}(hp:i≤k)(he:∀ j,i≤ j→j<k→Climate (dance X ν D' N j))(hx:1/2≤ R)(hu:Sense a U) : Sense a (ledgerR (dance X ν D' N) U a b k i):= by
   induction hp using Nat.decreasingInduction with
   | self=> rw [ledgerR,if_neg (lt_irrefl _)]; exact hu
   | of_succ i hi ih=> rw [ledgerR, if_pos hi]; exact creekS_w _ (he i (le_refl _) hi) (ih (fun j hp hz=> he j (by omega) hz)) hx _
lemma melody (X:Chain){U:Layouts I G D R}(x:E4)(p:I→ Profile D)(hp:i≤k)(he:∀ j,i≤ j→j<k→Climate (dance X ν D' N j))(hx:1/2≤R)(hu:Sense a U):
   sang X (ledgerR (dance X ν D' N) U a b k i) b p m i x= dustP X ν D' N k (vanes a univ) i (sang X U b p m k x):=by
   induction hp using Nat.decreasingInduction with
   | self=> rw [ledgerR,if_neg (lt_irrefl _),dust_top]
   | of_succ i hi ih=>
      have hk (j) (hp:i+1≤j) (hx:j<k):= he j (by omega) hx
      rw [dust_step _ _ _ _ _ _ _ _ hi,← ih hk, ledgerR, if_pos hi]; exact song_e X (he i le_rfl hi) hx (ledger_sense hi hk hx hu) p b x
section loci
variable {J Y:Type}{u:Y→Windows}{j:J}{W:J→ Dial u}{U:J→I→ℕ→BoardU D R G}
lemma strong_l (X:Chain)(p:I→Profile D)(v:List I)(he:v.Nodup)(hv:v.toFinset=univ)(ht:Attract ν D' X W U a b)(i:High W 0)(hp:∀ i:High W 1,Climate (heights X ν D' i.appr))(hx:1/2 ≤ R)(x:E4):
   sang X (ownerU X ν D' W U a b i.z i.i) b p i.K i.i x= waveProduct X ν D' i.K (W i.z).N x v a b p (U i.z) i.i:= by
   have hh s:= ht.leaf (High.mk (b:=W) (n:=0) i.z (W i.z).N (i.heap.trans i.scope) (le_refl _)) s
   have hH j (h:i.i≤ j)(he:j<(W i.z).N) := hp (High.mk i.z j (i.heap.trans h) he)
   let N:=(W i.z).N; have hp (j)(he:i.i≤ j)(hv:j < N):Climate (dance X ν D' N j):= hH j he hv
   have hez: vanes a univ= loadᵣ a v:= by rw [← listed_s he,hv]
   apply Eq.trans (melody X x p (m:=i.K) (b:=b) (U:=markZ (fun j=> U i.z j N)) i.scope hp hx (eyeSense hh)) _
   rw [hez, show sang X (markZ (fun j=> U i.z j N)) b p i.K _ _=marchFull X i.K x v b p (U i.z) N from sings_up (U i.z) v p x he hv (i:=N) hh b]; rfl
-- $t-m$ broaden rift; note ex stakes moves through broadening. Keep all changed ancestor labels in earlier legal masks: equality holds on profiles.
lemma banner_only {T: Finset I}{F Z:Topaz I (Tale G)} (hp:∀ p⊆T, F p=Z p) : Fabrics G F T=Fabrics G Z T:= by
    induction T using strongInductionOn with
    | _ t ih=>
      unfold Fabrics; rw [Wax.banner,Wax.banner]; split; next h=> rfl
      congr 1; apply sum_congr rfl; intro i hi
      have he:= (mem_filter.mp i.property).1
      have ⟨hv,hw⟩:= mem_product.mp (mem_filter.mp (show _ ∈ partners t from he)).1; congr 1
      · unfold sons; rw [hp _ (mem_powerset.mp hv)]
      exact ih _ (part_lt i.property) (fun t ht=> hp _ (Finset.Subset.trans ht (mem_powerset.mp hw)))
lemma lisp {U:Verts I}{F:Layouts I G D R} (hv: WardL U)(p:I→Profile D)(x:E4)(hp:∀ j∈cope X m k p x R,U j univ)(b:I→ℕ): sang X (rift U F) b p m k x=sang X F b p m k x:= by
    refine sum_congr rfl fun j hj=>congr_arg (lone X m k b • ·) (banner_only (F:=access _ ((rift U F) j)) (Z:=access _ (F j)) (fun i hi=>?_))
    unfold access rift; simp only [hv.reach _ _ (hp j hj) _ hi, ↓reduceIte]
-- complete story from top, reset at m and progress to b.
def joinerP (ν:G.ColorIndex)(D':ChartRatio G)(X:Chain)(p:J→Dial u)(U:J→ I→ℕ→ BoardU D R G)(a b:I→ℕ)(ρ:J→ℝ)(j:J) := rift (rural X.S (ρ j) (p j).K (p j).K) (ownerU X ν D' p U a b j (p j|>.K))
theorem broadened (v:List I)(he:v.Nodup)(hv:v.toFinset=univ)(ht:Attract ν D' X W U a b)(hx:1/2≤R)(hw:X.Wake G)(hC:LocalRatio D')(ψ:I→Profile D)(x:E4)(ρ:J→ℝ) (j:J)(i:ℕ)(ho:i ≤ (W j).K)(hT:∀ j'∈cope X (W j).K (W j).K ψ x R,rural X.S (ρ j) (W j).K (W j).K j' univ):
   sang X (vitalK ν D' X W (joinerP ν D' X W U a b ρ) a b j i) b ψ (W j).K i x=waveProduct X ν D' (W j).K (W j).N x v a b ψ (U j) i:= by
    have hh n m (hi:n<m):Climate (dance X ν D' m n):= ⟨fairground X ν D' hw hC hi, authentic hw ν D' _ _⟩
    have hk(i: High W 1): Climate (heights X ν D' i.appr):=hh _ _ i.appr.cut
    let s:= Harvest.beacon W j
    unfold vitalK; rw [melody X (U:=joinerP ν D' X W U a b ρ j) (hp:=ho) (he:=fun i hi hb=>hh _ _ (hb.trans_le (W j|>.main))) (hx:=hx) (hu:=riftStyle (owned_tv ht hk hx s).1 (rule_w ..)), joinerP,lisp (rule_w ..) ψ x hT]
    rw [show sang X (ownerU X ν D' W U a b j (W j).K) _ _ _ _ _=waveProduct X ν D' (W j).K (W j).N x v a b ψ (U j) (W j).K from strong_l X ψ v he hv ht s hk hx x]
    rw [show vanes a univ=loadᵣ a v by rw [← listed_s he,hv]]; exact Eq.symm (dust_on _ _ _ ho _ (W j|>.main))
end loci
end YM.RG08.Creek
