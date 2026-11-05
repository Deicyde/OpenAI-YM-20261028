import YM.UVExtension.Rainfall.Trail
import YM.UVExtension.Lacing.Bridge
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Rainfall
open Finset Function Filter Set MeasureTheory Lattice Wilson RG Source Labels Extra.Histories Bid
open Planned.GuardedAtom Push Local Guard Motion PhysicalNext.Repeat Lotus
open Eyelet MergeProof Lacing
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{d:ℕ}{F:Labels.Frame G d}(B:SectionData F) (H : History G) (N p m : ℕ) (A : Hol G)
open Extra.Histories.InputColumn
local notation "κ"=> Real.sqrt (H.levels.clock.forcedAllowance (m+1))
local notation "Λ"=> Real.sqrt (H.levels.clock.forcedAllowance m)
variable {T : Extra.Histories.Heading F} {C η t w : ℝ}
local notation "n"=> H.S.side m p
local notation "n'"=> H.S.side (m+1) p
local notation "Old"=> H.rep N p (m+1)
local notation "Out"=> H.rep N p m
local notation "F1"=> F.Coeff
set_option quotPrecheck false
structure Flees (E:Rep G n')(R:Rep G n)(D:GaugeDoor E R) (X:Set Wing) (α : Config G n'→ℂ)(ρ:Res G n') (ψ:ℂ) (g:Config G n'→ℂ) (v:F.Coeff) (c t w:ℝ)(q:Bucket F R.p A n) : Prop where
    mints: ∃ P:Coefficient F n, Gig B H N p m A g P v c t ∧ Tale X 0 0 (((H.S.block m).val:ℂ)^d) α ρ (profile R.activities P.forced) ψ w t D ∧ Eye P A R Λ=q
variable (E:Rep G (H.S.side (m+1) p)) (R:Rep G (H.S.side m p))(D:GaugeDoor E R)(X:Set Wing)
    (K:Keeper E.p E.activities)(L:RoutesF F (H.S.side m p) (H.S.side (m+1) p) E.p R.p A)
open MergeProof
structure Palace (r:Side)(V :Heading F)(C η t:ℝ): Prop where
    coins : Nonempty (Keeper R.p R.activities)
    route : L.route= cart (R:=E) K
    good : SoundDoor (H.levels.clock.op m p) D
    map_norm x: F.coeffSize (V.map x) ≤ C*F.coeffSize x ∧ F.coeffSize (V.map.symm x)≤ C*F.coeffSize x
    pivot i: let v:=seed F i; let P:=Extra.Histories.primary (0:Site n') v
             Flees B H N p m A E R D X (P.exponentialEntry 0 B E) 0 (v 0) (P.density 0 B E) (V.leads r v) (η*F.coeffSize (F.core v)) (C*F.coeffSize (vowel F r (F.core v))) (peat t (F:=F) i) (L.vane i)
    glass (i:Eyelet.Slot n') (j:Birth A i.1 E.p d) (c:ℝ): let u:= E.p.mass i.1.val c
              E.p.supBounds 0 i.1.val j.val c → Flees B H N p m A E R D X (masked E.p.threshold i.1.val j.val) 0 0 (salary E i.1.val j.val) 0 (η*u) (η*u) (2*u) (L.glass i ((Eyelet.fee E.p i.1.val:ℂ) • twig (tin d A i.1 E.p) j))
    wing  (i:StockTag (H.S.side (m+1) p)) (x:Eyelet.Bolt (G:=G) E.p i) (a:ℝ) : let j:= L.route i; let u:=E.p.mass i.val.1 a
               0 ≤ a → (∀ U, ‖x.val U‖ ≤ a) → Flees B H N p m A E R D X 0 (exactGas E.activities j x.val) 0 (Extra.Histories.fare E j x.val) 0 (η*(u/κ)) (η*(u/κ)) (2*u) (L.wing i ((((Eyelet.fee E.p i.val.1 / κ):ℝ):ℂ) • twig (sink (G:=G) E.p i) x))
variable (hr: H.rep N p m= R)(he: H.rep N p (m+1)=E)
def shim : Keeper (Old).p (Old).activities:= he.symm ▸ K
def ringS : RoutesF F n n' (Old).p (Out).p A:=hr.symm ▸ he.symm ▸ L
lemma seat (V' : RoutesF F n n' (Old).p (Out).p A)(t:ℝ){r:Side}(h:H.S.block m=r)(hp: Palace B H N p m A E R D X K L r T C η t)(hzL:HEq V' L) : Manor B H N p m A (shim H N p m E K he) (duet H N p m hr he D) X V' T C η t:=by
    subst E R r; obtain rfl:= eq_of_heq hzL; exact ⟨hp.coins, hp.route,hp.good,hp.map_norm,fun i=> ⟨(hp.pivot i).mints⟩,fun i j c hu=> ⟨(hp.glass i j c hu).mints⟩,fun i x a hV hU=> ⟨(hp.wing i x a hV hU).mints⟩⟩
include hr
lemma reaps {X' : ℕ→ Support n}{M:Push.Local.Raw F n}{w t u:ℝ}{f:Config G n'→ℂ}{v:F.Coeff}(hx:H.Conv N p m)(hR:Readable A B R.p n w)
    (h:Fancy B H N p m A f X' M v w t u)(K':Keeper R.p R.activities):
    Gig B H N p m A f (wallet K' X' B M A) v t u ∧ Attainment R.p 0 (coda B A 0 X' M R) u ∧ profile R.activities (wallet K' X' B M A).forced= profile R.activities M.forced + hook R.activities R.p.threshold (coda B A 0 X' M R) ∧ Valid M X' R (H.levels.clock.forcedAllowance m) B A w Λ:=by
   subst R
   obtain ⟨a,b,c,⟨h₁,h₂⟩,⟨S⟩,hv,⟨pQ,q,hq,h₃⟩,hA,hC⟩:=h; let S:= K'.supply (fun i=> joint B (0:Site n) (X' i)); let Z:= mint (R:=Out) S M A
   have hh:= (vigor hq h₁ hR)
   rw [h₃] at hh
   have hκ:0<kappa H m:= Real.sqrt_pos.mpr (forcedPos ..)
   have hp:Tab Z 0 Out (kappa H m) a (b+c):=tab_mint S h₁ hx.good hκ hR hv
   have htX:1≤ turnCost (Out).p.order (Out).p.power:= one_le_pow₀ (one_le_mul_of_one_le_of_one_le one_le_two (one_le_pow₀ one_le_two))
   refine ⟨⟨usage S h₁ hx.good hR,(value_mint S h₁ hx.good hκ hR hv).trans h₂,?_,_,_,hp,hA⟩,stackFee hh ((le_mul_of_one_le_left hp.first htX).trans ((le_add_of_nonneg_right hp.second).trans hA)),budgetProfile S hv h₁ hR hx.good hκ,h₁,_,_,_,hv⟩
   obtain ⟨f,e,h1,h2,h3⟩ | hP := hC
   · exact le_trans (mul_le_mul_of_nonneg_left (sensor S h₁ hR hv h1 h2) (zero_le_one.trans (orbitCost_one_le F))) h3
   exact le_trans (mul_le_mul_of_nonneg_left (size_mint S h₁ hR hv v) (zero_le_one.trans (orbitCost_one_le F))) hP
include he hr
lemma breeze {u t:ℝ}(ht:0≤ t)(hu:0≤u): Flees B H N p m A E R D X 0 0 0 0 0 t t u 0:=by subst E R; exact ⟨(leisure B H N p m A X _ ht hu).mints⟩
lemma dormant {C η t:ℝ} (T:Heading F) (r:Side) :
    let v:=seed F none; let P:=Extra.Histories.primary (0:Site n') v
    Flees B H N p m A E R D X (P.exponentialEntry 0 B E) 0 (v 0) (P.density 0 B E) (T.leads r v) (η*F.coeffSize (F.core v)) (C*F.coeffSize (vowel F r (F.core v))) (peat t (F:=F) none) 0:=by
   intro v P; have hv:v=0:=rfl
   have hJ:P.exponentialEntry 0 B E=0:=by
      funext U; change part B 0 E U (0:F.Coeff)+∑' i,P.maskedTerm E i U=0; rw [map_zero,zero_add]; simp_rw [show ∀ i,P.maskedTerm E i U=0 from fun i=> congr_fun (map_zero (Push.Local.maskLinear _ _)) _,tsum_zero]
   rw [hJ, show P.density 0 B E=0 from funext fun U=> by unfold P; rw [primary_density,hv,map_zero,mul_zero]; rfl, hv,Pi.zero_apply,map_zero (T.leads r),map_zero]; rw [show vowel F r 0=0 from funext fun i=>by simp [vowel], show F.coeffSize 0=0 from by simp [Frame.coeffSize],mul_zero,mul_zero]; exact breeze B H N p m A E R D X hr he le_rfl (by exact le_rfl)
lemma shrine (T:Heading F)(C w t:ℝ)(r:Side)(hz:H.S.block m=r)(hm:m<N)(hp:Vintage.YM.RG.History.Selected H)(hK : Keeper R.p R.activities)(hc:0≤ t): let v:= seed F (some 0); let P:= Extra.Histories.primary (0:Site n') v
    Flees B H N p m A E R D X (P.exponentialEntry 0 B E) 0 (v 0) (P.density 0 B E) (T.leads r v) (w*F.coeffSize (F.core v)) (C*F.coeffSize (vowel F r (F.core v))) t ((((r.val:ℂ)^d) • v),0):=by
   subst R E r; intro v P
   change Flees B H N p m A _ _ _ X _ _ (F.e0 0) _ (T.leads _ F.e0) (w*F.coeffSize (F.core F.e0)) (C*F.coeffSize (vowel F _ (F.core F.e0))) t _
   let L:= H.S.block m; let x:ℂ:= (L.val:ℂ)^d
   have hx : T.leads L F.e0=x • F.e0 := by
    change T.map (vowel F L F.e0) = _
    rw [show vowel F L F.e0 = x • F.e0 by
      funext i
      by_cases hi : i=0
      · rw [hi]; simp [x,vowel,F.zero_degree]
      simp [vowel,Frame.e0,Pi.single_eq_of_ne hi],map_smul,T.unit]
   rw [Size.unit_core, show vowel F L 0=0 from funext fun i=>by simp [vowel], show F.coeffSize 0=0 from by simp [Frame.coeffSize],mul_zero,mul_zero]
   let R:= Extra.Histories.primary (0:Site n) (x • F.e0)
   have hu:P.exponentialEntry 0 B Old= fun _=>1:=by
      funext U
      have he j:P.maskedTerm Old j U=0:= congr_fun (map_zero (Push.Local.maskLinear _ _)) U
      change F.e0 0+maskLinear _ _ (presented B 0 _ (F.core F.e0)) U+∑' j,P.maskedTerm Old j U=1; rw [Size.unit_core]; simp only [map_zero,Pi.zero_apply,add_zero,Frame.e0,Pi.single_eq_same,he,tsum_zero]
   have hκ:R.remBound 0 Out (kappa H m) 0:= primary_rem _ (Real.sqrt_pos.mpr (forcedPos _ _)); have hw:=hκ; obtain ⟨a,b,hb,hA⟩:= rem_tabs.mp hw
   have ha:a=0∧b=0:=by have h:=hb.first; have h':=hb.second; constructor<;> linarith
   obtain ⟨rfl,rfl⟩:= ha
   have hE:Eligible R A Out (kappa H m):=⟨⟨hK⟩,primary_format _,_,hκ⟩
   refine ⟨R, ⟨primary_format _,?_ ,?_, 0,0,hb,by simp⟩,?_,?_⟩
   · have hz : blast H N p m d (P.density 0 B Old)=x • liftVac H N p m:=by unfold P;rw [show v=F.e0 from rfl,unit_density]; exact Vintage.YM.Extra.Histories.blast_vac H N p m d hp hm
     unfold R; rw [hz,show Extra.Histories.primary (0:Site n) (x • F.e0) = Extra.Histories.stretch x (Extra.Histories.primary 0 F.e0) by simp [Extra.Histories.stretch,Extra.Histories.primary]]
     funext V; rw [stretch_density,_root_.YM.Extra.Histories.unit_density];rfl
   · rw [hx]; simp [R,Extra.Histories.primary,Frame.coeffSize]
   · rw [hu, show profile (Out).activities R.forced=0 by funext i j; simp [R,Extra.Histories.primary,profile,cram],Frame.e0,Pi.single_eq_same]; exact taped hc le_rfl
   rw [hE.vistas]; exact Prod.ext rfl (Prod.ext (Eligible.blankC hE|>.1) (Eligible.blankC hE|>.2))

end YM.UVExtension.Rainfall
