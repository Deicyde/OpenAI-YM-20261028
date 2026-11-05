import YM.RG08.Creek.East
/-! # Finer-kernel connected step estimates with base-root separations.
Supports ancestor restriction, without requiring the primitive to know $m$.
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.RG08.Creek
open Function Finset Filter RG Lattice Laurent Quire Vale Bloch Next.Free Stationary Shade Wax Town Bands Plot Needle Tall Scores Push.AbsoluteSums Work.F08 Door
open scoped Topology ContDiff BigOperators Real Classical Matrix
variable {I:Type} [Fintype I][DecidableEq I]{G:Gauge}{R v A B ρ:ℝ}{L:Side}{T: Finset I}{a:I→ℕ}{h:I→ℝ} {e r τ D m n:ℕ}
section range
-- ideals downward on insertion t; supports true cells absolute. Any later use can enlarge via stencil zero on omitted tests
abbrev Verts (I:Type):= Places I→Finset I→Prop
structure WardL (V:Verts I):Prop where
    reach (x:Places I)(t:Finset I): V x t→∀ s⊆ t,V x s
    only (t:Finset I)(x y:Places I): (∀ i∈t,x i=y i) → V x t=V y t
variable {V U:Verts I}{P:StripU G L}{F Z : Layouts I G D R}
def rift (V: Verts I)(F:Layouts I G D R): Layouts I G D R:= fun x t=> if V x t then F x t else 0
lemma rift_eq (V:Verts I)(F:Layouts I G D R): rift V (rift V F)=rift V F:= by funext x t; unfold rift; split_ifs <;> rfl
lemma riftStyle (he:Sense a F)(hp:WardL V): Sense a (rift V F):= by
   refine ⟨fun x t=>?_,fun x y t=>?_,fun x=>?_,fun t x y ht=>?_⟩
   · unfold rift; split; exact he.style ..; exact style_empty
   · unfold access rift; split; exact he.stone ..; exact (show Stone _ (0:Tale G) from Stone.zero) |> fun h=> by convert h using 1; ext; simp
   · unfold rift; rw [he.void]; split <;> rfl
   dsimp only; unfold rift; split_ifs with h hG h'; exact he.only t x y ht; rw [← hp.only t x y ht] at hG; contradiction; rw [hp.only t x y ht] at h; contradiction; rfl
-- output may use stronger restriction than full input masks; no arbitrary correlations inferred elsewhere.
def growsR (U V:Verts I)(L:Side):Prop:= ∀ x t, V x t→∀ p, U (footT L x p) t
lemma rS_eq (hz:rift U F=rift U Z)(ha:growsR U V L)(hq:WardL V): rift V (creekT P a h F)=rift V (creekT P a h Z):=by
    let S(x:Places I)(F:Layouts I G D R):= chancel L (signet L F x h)
    let W(x:Places I)(F:Layouts I G D R):= Wax.orbitV none (veiled P.cv) P.song (S x F)
    funext x t; unfold rift; split; next ht=>
       have hp (s:Finset I)(hs:V x s): S x F s= S x Z s := by
          unfold S chancel
          have hx(p:subroll s (Site L)):shop (enter s p) F x h s=shop (enter s p) Z x h s:=by
             have hh(α:I→Site L): F (footT L x α) s=Z (footT L x α) s := by
                have he:=congr_fun (congr_fun hz (footT L x α)) s; rwa [rift,rift,if_pos (ha x s hs _),if_pos (ha x s hs _)] at he
             unfold shop; rw [hh]
          rw [show signet L F x h s=signet L Z x h s from sum_congr rfl fun j _=>hx j]
       have hv n t (he:V x t): W x F t n=W x Z t n:= by
          induction n using Nat.caseStrongRecOn generalizing t with
          | zero=> unfold W; rw [orbit_z,orbit_z]; exact hp _ he
          | ind n ih=>
             let M:=veiled P.cv; let K:=P.song; let w(f:Layouts I G D R)(u:Finset I)(i:ℕ):= if h:i≤n then W x f u i else 0
             have hu i (h:i⊆t): w F i=w Z i:= funext fun j=>by unfold w; split; exact ih j ‹_› _ (hq.reach _ _ he _ h); rfl
             unfold W; rw [Wax.orbitV,Wax.orbitV]; refine congr_arg (fun z:Screed (Poise t D R) (Park G L)=> ((↑(n+1:ℕ)):ℝ)⁻¹•z) ?_; change Wax.blue none M K (w F) t n=Wax.blue none M K (w Z) t n; funext i j
             unfold Wax.blue; rw [hu t (subset_refl _)]; refine congr_arg₂ (·+·) rfl (congr_arg ((1/2:ℝ) • ·) ?_)
             apply sum_congr rfl; intro i h; obtain ⟨h,hp⟩:=mem_product.mp (mem_filter.mp h).1
             unfold spunL; rw [hu i.1 (mem_powerset.mp h),hu i.2 (mem_powerset.mp hp)]
       have hx : solar P a h F x t=solar P a h Z x t:= by
          funext i j; dsimp only [solar]; unfold noon; exact sum_congr rfl fun i _=> congr_fun (congr_fun (hv i t ht) _) _
       unfold creekT; unfold mature; rw [hx]
    rfl
lemma rift_pass (he:growsR U V L)(hp: WardL V): rift V (creekT P a h F)=rift V (creekT P a h (rift U F)):= rS_eq (rift_eq ..|>.symm) he hp
lemma rift_fe (h:Sense a F)(hp:WardL V)(hz: Owns v T (fun x=>F x T e r) B): Owns v T (fun x=>rift V F x T e r) B:= by
   refine ⟨fun x y hp'=>congr_fun (congr_fun (riftStyle h hp|>.only _ x y hp') e) r, hz.pos,fun a=>?_⟩
   obtain ⟨U,H,ht⟩:=hz.2.2 a; refine ⟨U,fun p=>?_,ht⟩
   unfold rift; dsimp only; split; exact H _; exact Ink.raise (Ink.none _ _) (Ink.nonneg (H _))
-- separation normalized on output. if T>1 r; spread≥ρ across ANY active T root. No mark list param. keep root Max. no tests lost on broaden.
def Vast (V:Verts I)(ρ:ℝ):Prop:= ∀ (x:Places I) (T:Finset I) (i:↥T) (j:↥T), V x T → i≠j → ρ ≤ (size (x i.val-x j.val):ℝ)
lemma sphere_for {p:Fleet T}(h:Vast V ρ)(hs: V (loose T p) T)(hx:1 < T.card)(a:T) : ρ ≤ (Mounts a p:ℝ):= by -- binder
    haveI : Nontrivial ↥T:= Fintype.one_lt_card_iff_nontrivial.mp (by simpa using hx)
    obtain ⟨b,hb⟩:= exists_ne a
    have hz:= h (loose T p) T b a hs hb
    rw [show loose T p b=p b from dif_pos b.property,show loose T p a=p a from dif_pos a.property] at hz
    exact hz.trans (Nat.cast_le.mpr (single_le_sum (s:=univ) (f:=fun j:T=>size (p j-p a)) (fun _ _=>Nat.zero_le _) (mem_univ b)))
lemma sun_step (h:Sense a F)(hp: WardL V)(ht:Vast V ρ)(hw:0 < v)(hz:Owns (2*v) T (fun x=> F x T e r) A)(hu:1<T.card): Owns v T (fun x=>rift V F x T e r) (Real.exp (-v*ρ)*A) := by
    refine ⟨fun x y hx=> congr_fun (congr_fun ((riftStyle h hp).only T x y hx) _) _, mul_nonneg (Real.exp_pos _|>.le) hz.pos,fun a=>?_⟩
    obtain ⟨X,hX,H⟩:= hz.2.2 a
    let P(p: Fleet T):=if V (loose T p) T then X p else 0
    have hx (p): Pail (p a) v (rift V F (loose T p) T e r) (P p):=by unfold P rift; split; exact Ink.shrink (hX p) (fun i=> Real.exp_pos _|>.le) (fun i=> Real.exp_monotone (mul_le_mul_of_nonneg_right (show v≤2*v by linarith) (by positivity))); exact Ink.none ..
    refine ⟨P,hx,fun x=> budget_mono (budget_scale (Real.exp_pos (-v*ρ)|>.le) (H x)) (fun i=> mul_nonneg (Real.exp_pos _|>.le) (Ink.nonneg (hx i.val))) fun i=>?_⟩
    unfold Tribe P; split; next hh=>
      have hs:= sphere_for ht hh hu a; rw [← mul_assoc,← Real.exp_add]; exact mul_le_mul_of_nonneg_right (Real.exp_monotone (by nlinarith only [hs,hw])) (Ink.nonneg (hX _))
    rw [mul_zero]; exact mul_nonneg (Real.exp_pos _|>.le) (mul_nonneg (Real.exp_pos _|>.le) (Ink.nonneg (hX _)))
end range
end YM.RG08.Creek
