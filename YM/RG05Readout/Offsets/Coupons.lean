import YM.MergeProof.Gelatin
import YM.MergeProof.Volley
import YM.RG05Readout.Offsets.Rows
/-!
# Moving-root one-mark ports at each horizon. Literal scalar root and indivdual
log/gas partners. Does not assert the analytic estimate or an addressed result scaled
at all positions. Calls on representatives sharing layout and post-coarse flag
companions. Adapt from `MergeProof.Gig`. 
-/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof
open Finset Function Filter Set MeasureTheory Lattice Wilson RG Source Labels Extra.Histories Bid
open Planned.GuardedAtom Push Local Guard Motion PhysicalNext.Repeat Lotus
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{d:ℕ}{F:Labels.Frame G d}(B:SectionData F) (H : History G) (N p i : ℕ) (Y : Hol G)
open RG05Readout.Offsets
set_option quotPrecheck false
local notation "Rout" => H.rep N p i
local notation "Old" => H.rep N p (i+1)
local notation "c'" => H.S.side i p
local notation "StartSite" => H.S.side (i+1) p
local notation "g₀" => Config G StartSite → ℂ
local notation "Lℓ" => H.S.block i
local notation "κ" => kappa H i
variable (b : Site (H.S.side (i+1) p)) (A : Wing→Prop)

/-- One inspected root. Costs at the pre/post threshold weights on Gig, carry
    the exact log/gas cut of Tale (not a statement about replacing density
    within a poly without emitting the accompanying mixed partners). -/
def Along (D:GaugeDoor Old Rout) (f:g₀) (g:g₀) (ν:Res G StartSite)(z:ℂ)
    (x:F.Coeff)(m k l:ℝ): Prop := ∃ (Q:Coefficient F c'), Gig B H N p i Y f Q x m k ∧
        Tale A b 0 (((Lℓ).val:ℂ)^d) g ν (profile (Rout).activities Q.forced) z l k D

structure Tracking (D: GaugeDoor Old Rout)(T:Heading F)(C α e:ℝ) : Prop where
   entry (j:F.Index) : j≠0→ let x:= Size.axis F j; let P:=Extra.Histories.primary b x
      let u:= C*F.coeffSize (vowel F (Lℓ) (F.core x))
      ∃ Q:Coefficient F c', Gig B H N p i Y (P.density b B Old) Q Q.x 0 u ∧
          F.coeffSize (basisCut F (F.grades j).1 (Q.x-T.leads Lℓ x))≤α ∧
          F.coeffSize Q.x ≤ u ∧
          Tale A b 0 (((Lℓ).val:ℂ)^d) (P.exponentialEntry b B Old) 0 (profile (Rout).activities Q.forced) 0 e u D
   regular (g : g₀)(a:Support StartSite)(c:ℝ) (hv: RegFit Old b d Y a g) (hk: (Old).p.supBounds b a g c) : let t:= (Old).p.mass a c
           Along B H N p i Y b A D (salary Old a g) (masked (Old).p.threshold a g) 0 0 0 (α*t) (α*t) (2*t)
   forced (g:g₀)(j:ℕ)(c:ℝ)(hv : SlotFit Old b j g)(h : g ≠ 0)(he: A (.gasKey j))(hg:∀t,‖g t‖≤c):
         let t:= (Old).p.mass ((Old).activities.forced j).support c; let u:= t/kappa H (i+1)
         Along B H N p i Y b A D (Extra.Histories.fare Old j g) 0 (exactGas (Old).activities j g) 0 0 (α*u) (α*u) (2*t)

-- `T` refers to the base heading (true centered calculation), also used before offsets
structure Pricing (D: GaugeDoor Old Rout) (T:Heading F) (hd : ℝ) (t r u:ℝ):Prop where
  buys : ∀ (b:Site StartSite), (H.levels.clock.op i p).ratio.parent b=0 →
       ∃ (Z': Keeper (Old).p (Old).activities),∃ X:Set Wing, X.Finite ∧
         (∀ i,X (.gasKey (cart Z' i))) ∧ Tracking B H N p i Y b X D T t r u
  soundD : SoundDoor (H.levels.clock.op i p) D
  norm x: F.coeffSize (T.map x) ≤ t* F.coeffSize x ∧ F.coeffSize (T.map.symm x) ≤ t* F.coeffSize x
  lower : Push.Local.Leading T.map.toLinearMap hd

section
variable {B H N p i Y b A} {g f:Config G (H.S.side (i+1) p) → ℂ}{ν:Res G (H.S.side (i+1) p)}{k z:ℂ}{y:F.Coeff}{t u m l q r a :ℝ}{D:GaugeDoor (H.rep N p (i+1)) (H.rep N p i)}
lemma Along.weaken (h:Along B H N p i Y b A D f g ν k y t u m)(ht:t≤l)(hu:u≤q)(hm:m≤r):
    Along B H N p i Y b A D f g ν k y l q r:=by
  obtain ⟨P,hP,hQ⟩:=h; exact ⟨P,hP.weaken ht hu,hQ.climb le_rfl hm hu⟩

end
section
variable (D:GaugeDoor (H.rep N p (i+1)) (H.rep N p i)){t u:ℝ} -- avoid
lemma empty_mark (ht:0≤t)(hu:0≤u) : Along B H N p i Y b A D 0 0 0 0 0 t t u:=by
   let P:Coefficient F c':= Extra.Histories.primary 0 0; have hp: P.Format 0 Y Rout:= primary_format _
   have he: P.density 0 B Rout=0:=by
      funext V; rw [show P.density 0 B Rout V= _ from primary_density B (Rout) 0 V];change _*part B 0 Rout V 0=0;rw [map_zero,mul_zero]
   have hκ: P.remBound 0 Rout (kappa H i) 0:= primary_rem _ (Real.sqrt_pos.mpr (forcedPos _ _)); obtain ⟨a,b',hb,h₁⟩:= rem_tabs.mp hκ
   have h2:a=0∧ b'=0:= by have hz:=hb.first; have hr:=hb.second; constructor<;>linarith
   obtain ⟨rfl,rfl⟩:=h2
   refine ⟨P,⟨hp,?_,by simpa only [P, Extra.Histories.primary,sub_zero,Frame.coeffSize,Pi.zero_apply,norm_zero,sum_const_zero,mul_zero] using ht, 0,0,hb,by rw [mul_zero,add_zero]; exact ht⟩,?_⟩
   · have hx:= (H.levels.transition_mass i p (Old).beta)
     rw [he,Extra.Histories.blast]; funext x; simp [StepData.push]
   rw [show profile (Rout).activities P.forced = 0 by funext i j; simp [profile,P,cram,Extra.Histories.primary]]; exact taped hu ht

lemma along_additive {ι : Type}[Countable ι][Nonempty ι]{f g:ι→ Config G (H.S.side (i+1) p)→ℂ}{ν:ι→ Res G (H.S.side (i+1) p)}{x:ι→ℂ}{v:ι→ F.Coeff}{u a z:ι→ℝ}{φ:g₀}{ψ:Res G StartSite}{σ:ℂ}
    (hq:SoundDoor (H.levels.clock.op i p) D)
    (h:H.Selected)(hm:i≤ N)
    (hh:∀ j, Along B H N p i Y b A D (f j) (g j) (ν j) (x j) (v j) (u j) (a j) (z j))
    (hg:∀ U,HasSum (fun i=>g i U) (φ U))(hx:∀ i U,HasSum (fun j=> ν j i U) (ψ i U))(ht:HasSum x σ)
    (hf:Dominated f)(hk:∀i,Measurable (f i)) (hv:Summable fun i=> F.coeffSize (v i))(hu:Summable u)(ha:Summable a)(hζ:Summable z):
    Along B H N p i Y b A D (fun U=>∑' i,f i U) φ ψ σ (∑' i,v i) (∑' i,u i) (∑' i,a i) (∑' i,z i):=by
   choose Q hQ Hq using hh
   let P:= Extra.Histories.merge (code _) Q
   have hκ:0<κ:= Real.sqrt_pos.2 (forcedPos ..)
   refine ⟨P,Gig.all_in B H N p i Y h hm hQ hf hk hv hu ha,Tale.upon hq Hq hg hx (fun i U=> profile_merge (code _) Q hκ (fun i=> (hQ i).bound) ha i U) ht ⟨fun i=>?_,hζ,le_rfl⟩ ⟨fun i=> rem_nonneg ((hQ i).bound),ha,le_rfl⟩⟩
   obtain ⟨ι,h,P,p,ψ,H⟩:= Hq i; exact sumBudget_credit H.purchase
end
end YM.MergeProof
