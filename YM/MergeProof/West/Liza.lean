import YM.Extra.MULTISOURCE_TRAJECTORIES.Initial
import YM.MergeProof.Pitch
import YM.MergeProof.West.Dink



set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Tapes.West
open Function Lattice Wilson RG Perch Atlas Rise Normal Ribbon Spindle Glyph Exponential MvPolynomial Camp Peak Station Ac Alarm Thirst Corona Value Relation Finset Marker
open MeasureTheory Cells Edition Filter
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius
variable {G:Gauge}{N n p k q i l j d D m u:ℕ} {C:Family G}{x:Points m} {ξ:Purse} {R:Lead G C.S p} {c:Course C N p k}{P:(i:ℕ)→ Rep G (C.side i p)}{s:ℝ}{Ψ:AtlasData G C.S p}
section
open MergeProof.Accent
variable (V:Fin m→ poly (Chamber G C.S k p))
private lemma starts_X (x:Chamber G C.S k p→ℝ) : t_cum R V le_rfl x= Mach (Stock.census (Fin m)) (fun i=> text x (V i)):=by
   apply (expanders R V le_rfl x).uniq
   refine ⟨MergeProof.Accent.mute ..,?_⟩
   ext i; rw [Mach, Extra.Trajectories.pass_fire]; change _= text x (heads _ _ _ i)
   rw [heads,center_shelf]; exact (map_prod (aeval (R:=ℂ) (fun i=>(x i:ℂ))) V i.val).symm
lemma strophe (v:modes (Fin m))(hp:2 ≤ v.val.card): vista R V le_rfl v=0 :=by
    apply audible; intro z; rw [show text z (vista R V _ v)=(t_cum R V le_rfl z).part v from rfl, starts_X (C:=C), hush _ _ hp]; exact (map_zero _).symm
lemma x_cept (i:Fin m): vista R V le_rfl (Glyph.slot i)=V i:= audible _ _ (fun z=>by rw [show text z (vista R V _ _)= (t_cum R V le_rfl z).part (Glyph.slot i) from rfl,starts_X (C:=C),MergeProof.Accent.sing])
end
section
variable (x : Points m)(j:Fin m)
def solitaire (ξ:Purse)(p : ℕ)(k : ℕ)(A:Levels G): PatchPt x ξ.band A p ξ.horizon (show k≤ k from le_rfl):=by
   refine ⟨⟨Glyph.slot j,singleton_nonempty _⟩,fun i hi t ht=> ?_⟩; obtain rfl:= mem_singleton.mp hi; obtain rfl:= mem_singleton.mp ht; rw [separation_self]; exact Nat.zero_le _
lemma x_head : Head (solitaire x j ξ p k C.path.levels).val=j:= mem_singleton.mp (head_member (solitaire x j ξ p k C.path.levels).val)
end
section
variable {d : Fin n → ℕ} (x:Points n)(v:(i:Fin n)→ C.label (d i))
   (F:(i:Fin n)→ StampDuty C k N p (d i) ξ.taylor (P k) ξ.era.coast.Q Ψ)
local notation "AX" => C.path.levels
local notation "B" => ξ.band
local notation "T" => Ship.yard C ξ.band c.allow p
local notation "Y" => (fun i => prefaced (F i) (v i) (Station.choose AX B k x i))
set_option quotPrecheck false
lemma kits (h:∀ i,coin ((F i).W (v i)) ≤ ξ.principal (clim C.path.levels k)) : Kith (A:=C.path.levels) Y x ξ:=by
   refine ⟨fun i=> le_trans (expend ..) (le_trans (expend ..) (h i)),fun i=> (totalDegree_rename_le ..).trans ((totalDegree_rename_le ..).trans ((F i).duration _)),fun i=>?_,fun i=>primed x (fun _=> v i) (F i) i _⟩
   unfold prefaced; rw [primeVisit]; exact poetry _ ((F i).crystal _) _ _

variable (Xg:Ceremony ξ c P R Ψ) (hv:Kith (A:=C.path.levels) Y x ξ)
    (hq:Caff (G:=G) ξ (clim C.path.levels k) (k-middle C.path.levels ξ.band k) u n)
include Xg
lemma x_journey (v' : (Ship.yard C ξ.band c.allow p).Cell) (j:Fin n)(g:ℝ)(U):
   let t:=solitaire x j ξ p k C.path.levels
   gloryFt (C:=C) x ξ.band p c.allow le_rfl (before AX B k) v' t.val g (vista R Y le_rfl t.val.val) U=
       dot ((T).hand v') (signet 0 g ((F j).W (v j)) (pull ((T).omega v') (seats C B x c.allow p (v',j)) U)):=by
   intro t; have ht:= journey x (fun _=> v j) (F j) Xg.sens c.allow j v' g U
   simp only [gloryFt]; rw [x_head x j (C:=C), show t.val.val= Glyph.slot j from rfl,x_cept (C:=C) (R:=R) Y j]
   simpa only [jacketPol,glory, polygon,oneRoot,center_shelf] using! ht
end
