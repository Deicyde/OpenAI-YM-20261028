import YM.RemainderComparison.Jolt.Pure
import YM.RemainderComparison.Lobby.Doses

/-!
# Land the vacuum scalar and the mark law on the same leaf roots.
 Alignment will symmetrise vacuum *residual plus mask leaks*, so no symmetry
 or test-independence of individual synthetic cash_io log answers implied.
 Includes total (Extensively constant but unmasked) as distinct address
 type even on marked runs. Retain after packing.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Lacuna
open Function Filter Finset Lattice RG Wilson MeasureTheory ProbabilityTheory Ovens
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Work.E03 Work.F03
open PhysicalNext PhysicalNext.Repeat Song Slide Trio
open AnalyticBridge VerifiedReset Collection Quotes YM.Extra.Iteration
open Mosaic Mosaic.Verse WickReps Flues Lobby
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G:Gauge}{c:Side}{ι β I : Type}{α:Type*}[DecidableEq β]
open Marker Serif
abbrev EmptyC : Marker.Census (Fin 0):= ⟨univ,mem_univ _,fun _=>mem_univ _,fun _ _ _=>mem_univ _⟩ -- auto params linter
variable (J : Marker.Census β) (u:Set ι)(k:ℕ)

def tint (x:ℝ): Poly J:= (x:ℂ) • 1
lemma tone (x:ℝ) : (tint J x).part J.quiet=(x:ℂ):=by unfold tint; rw [Poly.part_smul,Poly.one_part,if_pos rfl,mul_one]
lemma color : Injective (tint J):= fun i j h=> Complex.ofReal_injective ((tone J i).symm.trans ((congr_arg (fun f:Poly J=> f.part J.quiet) h).trans (tone J j)))
lemma tone_add (x y:ℝ): tint J (x+y)=tint J x+tint J y:=by unfold tint; rw [Complex.ofReal_add,add_smul]
lemma tintSum {c:I→ℝ} {s:ℝ}(hf: HasSum c s): HasSum (fun i=>tint J (c i)) (tint J s):= ((Complex.ofRealCLM.hasSum hf).smul_const ..) -- syntax
lemma paintless (m:Multiset ι)(h:Verse.load u m≠0): controls u (fun (_:ι)=> (0:Poly J)) m=0:=by
   induction m using Multiset.induction_on with
   | empty=> simp [Verse.load] at h
   | cons i m ih=> unfold controls; rw [Multiset.map_cons,Multiset.prod_cons]; split
                   next=> change 0 * _=_; exact zero_mul _
                   next hp=> rw [one_mul]; exact ih (fun hz=> h (by unfold Verse.load; rw [Multiset.filter_cons_of_neg _ hp]; exact hz))
lemma pureSong : Serif.Chorus EmptyC (fun _=>1) u (fun _=>0) k:=by
    refine Serif.production _ _ _ (fun _=>zero_lt_one) (by simp) (by simp) _ ?_ -- edit args
    intro v; exact (show v.val.card ≤ 0 from le_trans (Finset.card_le_univ _) (by simp)).trans (Nat.zero_le _)

variable (T:Manor G c ι α I)(P:BudgetPoint)(R:Vesuvius G c ι I α)
open Manor
local notation "Sʼ"=> Lobby.night T u
-- distinct resources.L

def aurora (a:α)(U:Config G c):= ∑' i:Sʼ,T.wet P a i.val U
def day (z:ι→Poly J) (a:α)(U:Config G c):= T.basin P (Sʼᶜ) u z a U

variable {J k u}{σ ψ d : ℝ}{root:ι→ Support c}{p:β→ℝ}
lemma peak {X:Set I} (hx:0 ≤ σ)(hp:T.Templary X root P σ d)(a:α)(U:Config G c): Summable (fun i:X=> T.wet P a i.val U):=by
    obtain ⟨f,h,hV,hF⟩:=hp.grants; exact Summable.of_norm_bounded ((Manor.arrival hF h hx).subtype X) (fun i=> Manor.wet_le a U (hV _ i.prop|>.1) ((hV i.val i.prop).2 a)) -- edit
lemma sunset (z : ι→Poly J)(a:α)(U:Config G c)(hp:T.Templary Set.univ root P σ d)(hσ:0≤ σ)(h: Chorus J p u z k): T.basin P Set.univ u z a U=tint J (aurora u T P a U)+day J u T P z a U:=by
   let f:= T.paint P u z a U; have hv:= Lobby.standing' P a u z T U hp hσ h; rw [Lobby.Univ]
   have ht: (∑' i:Sʼ,f i.val)= _ := ((Lacuna.tintSum J (peak T P (X:=Sʼ) hσ (hp.skim (Set.subset_univ _) le_rfl le_rfl) a U).hasSum).congr_fun (g:=fun i:Sʼ=> f i.val) (fun i=>by unfold f Manor.paint; rw [Flues.cold u z _ i.prop]; rfl)).tsum_eq
   exact Eq.trans ((Summable.tsum_add_tsum_compl (hv.subtype (Sʼ)) (hv.subtype _)).symm) (congr_arg (·+ _) ht) -- infer comp
lemma blankDay (V:Config G c)(a:α): Lacuna.day J u T P (fun _=>0) a V=0:=by
   apply (tsum_congr (g:=fun _=> (0:Poly J)) ?_).trans tsum_zero; intro i; unfold Manor.paint; rw [Lacuna.paintless J u _ (show Verse.load _ _≠0 from i.prop)]; exact smul_zero _

def shade (u:Set ι): Set I:= {i | Verse.load u (R.opus i)=0}
local notation "Vʼ"=> Lacuna.shade R u

def wray (u:Set ι) (a:α)(U:Config G c):= ∑' i: ↑(shade R u), R.log a i.val U
def mark (u:Set ι) (z:ι→Poly J)(a:α)(U:Config G c):= ∑' i : ↑((shade R u)ᶜ), Vesuvius.books a u z R U i.val
lemma barm (hx: R.Works P root u σ d ψ) (hσ:0 ≤ σ)(a:α)(U: Config G c): Summable (fun i: Vʼ=>R.log a i.val U):=by
    obtain ⟨f,g,hf,hg,h,h',hV⟩:=hx.fortune
    have he:= Product.everyone_ne R.site P.B hf (fun i _=> R.yeah i) h
    have hv:Summable f:= he.2.1.of_nonneg_of_le hf (fun i=> le_mul_of_one_le_right (hf i) (Real.one_le_exp (mul_nonneg hσ (by positivity))))
    exact Summable.of_norm_bounded (hv.subtype _) (fun i=> by change _ ≤ f i.val; rw [← if_pos (show Verse.load _ _=0 from i.prop) (t:=f i.val) (e:= g i.val)]; exact hV ..)
lemma farm (z:ι→ Poly J)(a:α)(U:Config G c)(hp:R.Works P root u σ d ψ)(hσ:0≤ σ)(h: Chorus J p u z k): ∑' i, Vesuvius.books a u z R U i= tint J (wray R u a U)+Lacuna.mark R u z a U:=by
    let Q := Vesuvius.books a u z R U
    have hg:Summable Q:= Vesuvius.pi_support P root k a u z R hp hσ h U
    have hx : (∑' i: ↑(shade R u),Q i.val)=_:= ((Lacuna.tintSum J ((barm P R hp hσ a U).hasSum)).congr_fun (g:=fun i: ↑(shade R u)=>Q i.val) (fun i=>by unfold Q Vesuvius.books; rw [Flues.cold u z _ i.prop]; rfl)).tsum_eq
    exact Eq.trans ((Summable.tsum_add_tsum_compl (hg.subtype (shade R u)) (hg.subtype _)).symm) (congr_arg (·+ _) hx)
lemma blankMark (V:Config G c)(a:α): Lacuna.mark (J:=J) R u (fun _=>0) a V=0:= (tsum_congr (g:=fun _=> (0:Poly J)) (fun i=> (by unfold Vesuvius.books; rw [Lacuna.paintless J u _ (show Verse.load _ _≠0 from i.prop)];exact smul_zero _))).trans tsum_zero
end YM.RemainderComparison.Lacuna
