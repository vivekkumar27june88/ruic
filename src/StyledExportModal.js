import FormControl from '@material-ui/core/FormControl';
import IconButton from '@material-ui/core/IconButton';
import List from '@material-ui/core/List';
import Paper from '@material-ui/core/Paper';
import styled from 'styled-components';

export const IconButtonStyled = styled(IconButton)`
    align-self: flex-end;
    color: darkgray;
    padding: 1rem;
    margin-right: 0.5rem;
`;

export const MainContainerStyled = styled(Paper)`
    elevation: ${({ theme }) => theme.elevation};
    margin: 0 1rem 2rem 1rem;
    border-top: 5px solid teal;
    box-shadow: 0px 2px 5px grey;
`;

export const MyPaper = styled.div`
    top: 0;
    height: 100vh;
    width: 50%;
    min-height: 450px;
    min-width: 500px;
    right: 0px;
    display: flex;
    flex-direction: column;
    padding: 0;
    position: absolute;
    background-color: ${({ theme }) => theme.palette.background.paper};
    box-shadow: ${({ theme }) => theme.shadows[5]};
    padding: ${({ theme }) => theme.spacing.unit * 4};
    outline: none;
`;

export const ExportOptionHeaderStyled = styled.div`
    display: flex;
    flex-direction: row;
    justify-content: space-between;
    align-items: center;
    margin: 1rem;
`;

export const ExportOptionSelectStyled = styled(FormControl)`
    width: 50%;
`;

export const ExportFieldSelectionContainerStyled = styled.div`
    margin: 3rem 1rem 1rem 1rem;
`;

export const SelectionListContainerStyled = styled.div`
    display: flex;
    justify-items: flex-start;
    flex-direction: row;
    justify-content: space-between;
`;

export const ColumnSelectionListStyled = styled(List)`
    border: 1px solid darkgray;
    margin-right: 0.5rem !important;
    flex: 1;
    max-height: calc(100vh - 230px);
    overflow-y: scroll;
`;

export const RegionSelectionListStyled = styled(List)`
    border: 1px solid darkgray;
    margin-left: 0.5rem !important;
    flex: 1;
    max-height: calc(100vh - 230px);
    overflow-y: scroll;
`;
