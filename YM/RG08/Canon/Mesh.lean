import YM.RG08.Canon.Palisade
import YM.RG08.Curl.Gust
/-! # Ergo, Armies on actual mesh and ANY planned Kin with canonical
 rules. Don't assert actual chosen Wilson labels path real-density.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG08.Canon
open Filter MeasureTheory YM.PertExtension.Series.Tested
open Function Analysis Tree Lattice RG Stationary Wilson Precision Exterior Laurent Finset Next.Free Matrix FreeResolvent Reflect Bloch UVExt.Paths Conductor
open PertExtension.Series.Radial PertExtension.Chart PertExtension.GaussianScore
open scoped BigOperators Topology Real ContDiff Classical Matrix.Norms.Frobenius
variable {G:Gauge} {H : Levels G} {s:Supply.Sheet G} {L : Supply.Rolls s} {M : PostCost L} {B:Horizon H} {D:ChartRatio G} {F:Kin B D}
variable (K : F.Planned M) (ν : G.ColorIndex)
local notation "X" => Chain.actual H
abbrev sameC {H:Levels G}{B:Horizon H}{D:ChartRatio G} (F:Kin B D)(ν:G.ColorIndex) (N m : ℕ) := ∀ k, Cask (H.params m).clip (F.path N m) (H.S.side m k) (Chain.column G (Chain.actual H) N m) ((Chain.actual H).album ν D N m)
include K
lemma same_begin (N : ℕ): sameC F ν N N := by
  intro k; unfold Chain.column Chain.K₀; rw [Chain.metric_wilson,Chain.album_top]
  let Q:= quad G (YM.RG08.hessian leader); let n:=H.S.side N k; let c:=(H.params N).clip
  let W:= wilsonTop ν; let R:=F.path N N
  have he i : recital (sector Q W 0 i) n= Tensor.coeff (WilsonQ G n) i 0 := by
    unfold Q; rw [← caramel_two ν]; exact Virtue.ref_score ν 0 n i
  refine ⟨(strain c R (K.cap N N le_rfl)).analytic.contDiffAt,fun j hj=>?_, (turns_analytic R.loop (K.cap N N le_rfl|>.width) (K.cap N N le_rfl|>.two) (m:=n)).contDiffAt,fun j hj=>?_⟩
  · exact (innate (K.peak N k j hj)).trans (he j).symm
  change Tensor.coeff (loopFn R (f:=n)) j 0=recital (sector Q W 1 j) n
  have hl : loopFn R (f:=n)=0:= by
     funext x; unfold loopFn loop Patch.average uncut Atom.unmasked Atom.poly; dsimp only [R]; simp_rw [K.initial]; simp
  rw [hl]; unfold Q; rw [← caramel_two ν]; exact (Virtue.ref_score ν 1 n j).symm

lemma same_next {m N:ℕ} (h:m<N)(he:sameC F ν N (m+1))(hG:G.Simple)(hp:LocalRatio D) :
    compass ν ((Chain.actual H).compassRaw ν D N m) 1= F.alpha N m ∧ sameC F ν N m := by
  let R:= F.path N (m+1); let T:= F.path N m; let p:= (H.params (m+1)).clip; let q:= (H.params m).clip
  have hv:=Chain.wake_actual H
  let a:= Chain.actual H; let P:= a.patch m; let t:=a.kernel; let w:= a.history N (m+1); let F':= a.trees m
  let S j:= H.clock.op m j; let V:= Chain.column G a N m; let J:=a.metric N m; let f:= H.S.side (m+1); let c:=H.S.side m
  let F0 j:= F'.forest (S j).ratio; let r(j):=F.stationary N m j (F0 j)
  let Z:= a.compassRaw ν D N m; let W:= a.album ν D N (m+1); let Y j := veil P t F' w ν D (some (c j)) W
  have hh := (a.packing ν D hv hp h)
  have hm:= a.metric_whole N m
  have hq:= a.metric_sym N m
  have ht := (conditional_truth G F' t (P:=P) w (hv m)).1
  have hs : Whole (coarseMean G F' t (P:=P) w) := (ht.prod ((probe_recites G P t).1.flipped)).weight _
  have hL := Chain.side_infinite H.S m
  have he' : SummitC S F0 p q R T r D V Y Z :=
     ⟨fun i=> by
         have hx : (f i).val=(c i).val*P.L.val:= (H.S.oneStep m i).exact_size
         have hX:=a.canonical N m h (c:= c i) (f:= f i) hx
         let e : ℝ:=M.η (H.clock.J (m+1)); have hb : 0<e:= M.price _
         exact staunch P t F' w ν (p:=p) hx J hm hq _ hX (hv m) hp hG hh.gets hh.halt (hh.opens _) (K.cap N (m+1) h) (he i) _ (K.critical N m i h (F0 i)).1 (K.gap N m i h (F0 i)) hb,
       fun i=>K.classicalPart N m i h _, WarmExhale ht hs (Gets_awake P D t ν hh.gets)|>.2 c hL, fun j=>(exhale_deck ht hs (Gets_awake P D t ν hh.gets) (some (c j))).2⟩
  obtain ⟨hV,hW,hB⟩:= a.high_stocks ν N m
  have hk : a.album ν D N m= correct ν Z V:= a.album_step ν D h; have hz := a.packing ν D hv hp h.le
  rw [hk] at hz; have hi := a.rawStep ν D hv hp h
  unfold sameC; rw [hk]
  apply post_float he' (K.cap N m h.le) (fun i=> ⟨hz,hi.2 i⟩) hB hi.1 hV hW hL hG (fun i=>K.retains N m i h (F0 i)) (M.pos _|>.le) _ (M.posC _)
  unfold Calendar.loopCap Calendar.monitor; positivity
-- all, period-independent histories
lemma planned_pay (hG:G.Simple)(hp:LocalRatio D) (N m : ℕ)(hm:m≤N) : sameC F ν N m := by
  induction hm using Nat.decreasingInduction with
  | self=> exact same_begin K ν _
  | of_succ i hi hI=> exact (same_next K ν hi hI hG hp).2
lemma planned_turn (hG:G.Simple)(hp:LocalRatio D)(N m:ℕ)(hm:m<N) : compass ν ((Chain.actual H).compassRaw ν D N m) 1 = F.alpha N m:= (same_next K ν hm (planned_pay K ν hG hp _ _ hm) hG hp).1


lemma independent_two (hG:G.Simple)(hp: LocalRatio D) (N m:ℕ)(hm:m<N) :
   |probeK ν ((Chain.actual H).compassRaw ν D N m 2 2)+ G.slopeConstant*Real.log (H.S.block m).val|+1 ≤ (H.params (m+1)).drift := by
  have hq:= planned_turn K ν hG hp N m hm; rw [Conductor.compass,if_neg (by decide),mul_one] at hq
  rw [hq]; exact K.kinetic _ _ hm
end YM.RG08.Canon
