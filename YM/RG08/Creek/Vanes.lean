import YM.RG08.Creek.Step
/-! # Step qualification on absolute cover. Preserves subset ideals.
Coherence for every occupancy (also inactive). Integrated evaluation and roll relations preserved at active loads.
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.RG08.Creek
open Function Finset Filter RG Lattice Laurent Quire Vale Bloch Next.Free Stationary Shade Wax Town Bands Plot Needle Tall Scores
open scoped Topology ContDiff BigOperators Real Classical Matrix
variable {I:Type} [Fintype I][DecidableEq I]{G:Gauge}{L:Side}{R:ℝ}{a:I→ℕ}{b:I→ℝ}{x y:Places I}{D:ℕ}{P:StripU G L}{F:Layouts I G D R}
lemma sign_o (h:Sense a F)(L:Side)(b:I→ℝ)(T:Finset I): Only T (fun x=> signet L F x b T):= by intro x y hp; refine sum_congr rfl fun i hi=>?_ ; unfold shop; rw [show F (footT _ x _) T= F (footT L y _) T from h.only T _ _ fun j hj=>?_]; unfold footT; rw [hp j hj]
lemma solar_o (h:Sense a F) (P:StripU G L)(b:I→ℝ)(T:Finset I): Only T (fun x=> creekT P a b F x T):=by
   let S (x:Places I):= chancel L (signet L F x b); have he(T:Finset I): Only T (fun x=> S x T):= fun x y hp=>by dsimp only [S]; unfold chancel; rw [show signet L F x b T= signet L F y b T from sign_o h L b T x y hp]
   let N:=veiled P.cv; let B:=P.song; let Ω (x:Places I):= Wax.orbitV none N B (S x)
   have hx n t: Only t (fun x=> Ω x t n):= by
     induction n using Nat.caseStrongRecOn generalizing t with
     | zero=> exact fun x y k=> by dsimp only [Ω]; rw [orbit_z,orbit_z]; exact he _ x y k
     | ind n ih=>
       intro x y hp
       let v (x:Places I)(i:Finset I)(j:ℕ):= if hz:j≤n then Ω x i j else 0
       have hX (i: Finset I)(h:i⊆t) : v x i=v y i:= funext fun j=>by unfold v; split; exact ih j ‹_› _ x y (fun a ha=> hp _ (h ha)); exact rfl
       dsimp only [Ω]; rw [Wax.orbitV,Wax.orbitV]; refine congr_arg (fun z:Screed (Poise t D R) (Park G L)=> ((↑(n+1:ℕ)):ℝ)⁻¹•z) ?_; change blue none N B (v x) t n= blue none N B (v y) t n; funext i j
       unfold Wax.blue; rw [hX t (subset_refl _)]; refine congr_arg₂ (·+·) rfl (congr_arg ((1/2:ℝ) • ·) ?_)
       apply sum_congr rfl; intro i h; obtain ⟨h,hp⟩:=mem_product.mp (mem_filter.mp h).1
       unfold spunL; rw [hX i.1 (mem_powerset.mp h),hX i.2 (mem_powerset.mp hp)]
   have hh : Only T (fun x=>solar P a b F x T):= fun x y k=>funext fun i=>funext fun j=>by dsimp only; unfold solar noon; apply sum_congr rfl; exact fun n _=>congr_fun (congr_fun (hx n T x y k) i) j
   intro x y k; dsimp only [creekT,mature]; rw [show solar _ _ _ _ x T= solar _ _ _ _ y T from hh x y k]

structure Climate (P:StripU G L) : Prop extends Fair P where
   even : ∀ m,(veiled P.cv|>.acts m)ᵀ=(veiled P.cv|>.acts m)
lemma creekS_w (L:Side){P:StripU G L}(hk: Climate P)(h:Sense a F)(he:1/2≤R)(b:I→ℝ) : Sense a (creekT P a b F):= by
   have ht (x:Places I)(t:Finset I) : Styled (vanes a t) (creekT P a b F x t):= crest_style h hk.toFair he; have hv x: creekT P a b F x ∅=0:= solar_z h hk.toFair he
   refine ⟨ht,fun x v=> banner_back (fun t=>?_) (fun t=>access_p (fun t=>(ht x t).tidy) (fun t=>(ht x t).cap) t v) (access_nil v (hv x)),hv,solar_o h P b⟩
   rw [banners_y h hk.toFair he hk.even]; exact inscribe_law _ hk.toFair (stone_p (sign_w h hk.odds he) _)
-- THEOREM identity for Wilson input including placements and gauge. Applies on ALL origins, present iff sensor receipts.
abbrev SolarPaper (F:Layouts I G D R)(x: Places I)(b:I→Sight D R)(T: Finset I):= Fabrics G (access b (F x)) T
lemma crest_p (h:Climate P)(hp:1/2≤R)(he:Sense a F)(x: Places I)(d:I→Sight D R)(T:Finset I):
   SolarPaper (creekT P a b F) x d T= inscribed (vanes a T) P 0 (∑ p:subroll T (Site L),(∏ i∈T,b i) • SolarPaper F (footT L x (enter T p)) (spar (enter T p) h.odds hp d) T):=by
   rw [SolarPaper,banners_y he h.toFair hp h.even, sign_s h.odds hp]
   let g(p:I→Site L)(t:Finset I):=preface F x p b h.odds hp d t
   have hf p t : Stone (vanes a t) (g p t):= (he.stone ..).weight _
   have hg t : scope t (fun p=>g p t):= fun p q hv=>congr_arg ((∏ i∈t,b i) • ·) (only_sh he x d h.odds hp t p q hv)
   have hZ p:g p ∅=0:= by unfold g preface; rw [access_nil _ (he.void _),smul_zero]
   rw [← convent_g hf hg hZ]
   refine congr_arg (inscribed _ _ _) (sum_congr rfl fun i _=> guill (a:=a) (he.stone (footT L x (enter T i)) _) b T)
end YM.RG08.Creek
