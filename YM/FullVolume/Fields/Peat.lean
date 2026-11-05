import YM.FullVolume.Fields.Pond
set_option autoImplicit false
noncomputable section
namespace YM.FullVolume.Sever
open Function Filter Set MeasureTheory Lattice Wilson RG Source Push Marker Extra.Histories Ac Bid Local
open Planned.GuardedAtom MergeProof MergeProof.Accent MergeProof.Menu Motion Extra.Multi Next.Rank Next.Rank.Spindle Finset
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {V:Type}[Fintype V][DecidableEq V]{B:Census V}{G:Gauge}
variable (C:Family G) (d: V →ℕ)(s:(i:V)→ C.label (d i)) (p k N j:ℕ) (o:∀ m:ℕ,V→ Site (C.side m p)) (g:V→Motion)
variable {W: Bid.Worth}{u ψ φ δ:ℕ→ℝ}{ζ:ℕ→ℕ→ℝ}{r:ℕ→ℕ}
     {D:∀ N p m:ℕ,m<N→GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
local notation "A"=>C.path
local notation "Q"=>C.path.rep N p
local notation "T"=> C.localSection
local notation "P"=> C.path.levels.budget
set_option quotPrecheck false
-- θ total from origin `s` after terminal inverse. not mixed.
def harp (m i):= indexX C (d i) N p (s i) (fun j=> o j i) (g i) m
def chill (m i):= Ktone C (d i) N p (s i) (fun j=>o j i) (g i) m
def seed (i:V):= item C (d i) N p (s i) (fun j=>o j i) (g i)
local notation "θ"=> harp C d s p N o g
local notation "χ"=> chill C d s p N o g
local notation "F!"=> seed C d s p N o g
abbrev Cresting (Y:B.Mode): ℂ:= stamp C.path N p j (restore (Q j) (θ j) (χ j) 0 0) Y
def pilot (Y:B.Mode): ℂ:= moment (C.beta N p) (fun U=> ∏ i∈ Y.val,F! i U)
-- meas normalized next. prove only need C.path.Selected. birth actual Wilson and moment when [Census].
variable (h:C.path.Selected)
section grant
include h
lemma equality (H:V→ Config G (C.side N p)→ℂ)(hH:∀ i, Continuous (H i))(a:B.Mode): moment (C.beta N p) (fun U=> ∏ i∈a.val, H i U)=stamp C.path N p N (Accent.birth B (Q N) H) a:=by
    let F':=fun U=> ∏ i∈a.val,H i U; let x:=C.beta N p
    rw [moment_formula _ F' (continuous_integrable x (continuous_finsetProd _ fun i _=>hH i))]
    unfold stamp; simp_rw [Accent.birth, (h.starts ..).2, Poly.part_smul,Mach, Extra.Trajectories.pass_fire]; rw [div_eq_mul_inv,mul_comm]
end grant
variable {Z:V→ℝ}(hh:Ponds C W u ψ φ δ ζ r D p k N)(hs:∀ i,(C.localSection (d i)).Sound C.params)(he:∀ i,C.ref (d i)≤ k)(hM:∀ i,Z i* Next.Rank.Spindle.paid C (d i) k N p (s i)≤ ζ (d i) k)(hw:∀ i,0< Z i)
variable (hx:Occupancy (o k) (r k))(hz:Drake B (C.path.levels.budget k).B (o k))(hy:Migrating C.path k p N o)
local notation "X"=> march Z φ k
variable (hV:j<N)(hf:k<j)(ha:Drake B (C.path.levels.budget j).B (o j))(hX:0≤ (C.path.levels.budget j).supportExponent-2)(hc:2 < brisk (C.path.levels.budget j).B)
variable {x y t v:ℝ} (heJ: Vault (march Z φ k j) (harp C d s p N o g j) (chill C d s p N o g j) t v)(hp:Vault Z (harp C d s p N o g k) (chill C d s p N o g k) x y)(hq:∀ i, Measurable (harp C d s p N o g j i))(hφ:∀ i p',Measurable (chill C d s p N o g j i p'))
include hw hx hz hy hV hf hX hc ha heJ hp hq hφ hh hs he hM h
set_option maxHeartbeats 500000 in
lemma echoes (a:B.Mode): ‖pilot C d s p N o g a-Cresting C d s p N j o g a‖ ≤ refreeze C.path.levels p k x y a Z/(brisk (P j).B/2):=by
    let F:= seed C d s p N o g; let f:=harp C d s p N o g; let φ':=chill C d s p N o g
    let J:= Accent.birth B (Q N) F; have ht : k ≤ N:= (hf.trans hV).le
    obtain ⟨G',H,Hg⟩:= hh.past C d N k p W u ψ φ δ ζ r D s o g Z h hs he ht hx hy hz hM hw -- hG syntax. implicit.
    have hK(i):Nectar C.path u D p N k o X f G' F i:=H i
    let w:= X; have hS:= desal C.path r k p N δ φ o Z hw hh.stay B hy hz hh.mom hx; let Y:= gust C.path N p N J
    have hxF(i:V):Continuous (F i):=by unfold F seed item stepUp Motion.scalar;split; exact ((C.continuousO ..).comp (continuous_pull ..)).star; exact (C.continuousO ..).comp (continuous_pull ..)
    have hj : Integrable J (prior G _):=by
       apply (Continuous.integrable_of_hasCompactSupport ?_ (HasCompactSupport.of_compactSpace _)); unfold J Accent.birth
       have hz:= show Continuous (Q N).eval from (by rw [(h.starts ..).2];exact bare_cont _)
       exact (Complex.continuous_ofReal.comp hz).smul (Poly.pass_cont.comp (continuous_finsetSum _ (fun i _=>(smeasure (B.fire i)).comp (hxF i)))) -- smeasure is continuous
    have hh₀ : Y N le_rfl=J:=gust_base ..
    obtain ⟨hf',hu,hg⟩:= Frost.upper C.path r δ u D p N o w f G' F (q:=Y) h ht hS hh.night hK (fun j _ he=> gust_step C.path N p N J he) hh₀ (hh₀.symm ▸ hj) j hf.le hV.le
    have hM:= Hg j hf.le hV.le
    have hA:topPitch C.path N j=(P j).supportExponent:=if_neg hV.ne; rw [hA] at hg
    have hT (i:V): Wakes C.path k j N p (fun m=>o m i) (fun m=> w m i) (fun m=> f m i) (fun m=> G' m i) D hV.le:=⟨fun m hm he=> (hK i).stocked _ hm (he.trans hV.le),fun m hm he=> (hK i).sways m hm (he.trans hV),fun m hm he=>(hK i).feeds m hm (he.trans hV)⟩
    have hF := desal C.path r k p j δ φ o Z hw hh.stay B ⟨fun i hi he=>hy.mare i hi (he.trans hV)⟩ hz hh.mom hx
    have hρ : w k = Z:= marines k φ Z hw
    have hP:= omissions C.path N p h hV.le hh.night hT hf hF ha (hh.stay.support j hf.le) hc hX hq (by rw [hM]; exact hφ) (show Vault (X j) (f j) (tapes C.path p N G' j) t v from by rw [hM]; exact heJ) (show Vault (X k) (f k) (tapes C.path p N G' k) _ _ from (by rw [show X k= Z from hρ,Hg k le_rfl ht]; exact hp)) hg a
    rw [hM,hρ] at hP
    have hk:pilot C d s p N o g a= stamp C.path N p j (Y j hV.le) a:= by
       rw [show pilot C d s p N o g a= _ from equality C p N h _ hxF a]; unfold stamp; let L:= (Poly.get a).restrictScalars ℝ; congr 1; exact ((L.integral_comp_comm hf').trans ((congr_arg L (gust_sum C.path N p N J hj hV.le)).trans (L.integral_comp_comm hj).symm)).symm
    rw [hk]; exact hP
end YM.FullVolume.Sever
#print axioms YM.FullVolume.Sever.echoes
